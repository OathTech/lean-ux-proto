import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFreshReceiver
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerCausalProjection

/-! The shared handshake observer preserves newest-admission attribution when
its supplied session and keepalive callbacks retain admission history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFresh.Worker
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources HandshakeCausal HandshakeWorker
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private theorem lift (a : WG.M α) : Preserves (liftWGPrefix a) :=
  StatePrefixEnsures.lift a (fun _ _ _ hi => hi) (fun _ _ _ _ _ _ hi _ => hi)
private theorem pure (x : α) : Preserves (Pure.pure x) :=
  StatePrefixEnsures.pure x (fun _ _ _ hi => hi) (fun _ _ _ hi => hi)
private theorem pure_ready (pid : PeerId) (x : α) : StatePrefixPreserves (Ready pid) Safe (Pure.pure x) :=
  StatePrefixEnsures.pure x (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)

private theorem chain (g : WGPrefix Event α) (next : α → WGPrefix Event β)
    (hg : Preserves g) (hn : ∀ x, Preserves (next x)) : Preserves (g >>= next) :=
  StatePrefixEnsures.bind hg hn
private theorem chain_ready (pid : PeerId) (g : WGPrefix Event α) (next : α → WGPrefix Event β)
    (hg : StatePrefixPreserves (Ready pid) Safe g)
    (hn : ∀ x, StatePrefixPreserves (Ready pid) Safe (next x)) :
    StatePrefixPreserves (Ready pid) Safe (g >>= next) := StatePrefixEnsures.bind hg hn

private theorem choice {I : List Event → WGWorld → Ambient → Prop} {Q : α → List Event → WGWorld → Ambient → Prop}
    (p : Prop) [Decidable p] (a b : WGPrefix Event α)
    (ha : StatePrefixEnsures I Safe a Q) (hb : StatePrefixEnsures I Safe b Q) :
    StatePrefixEnsures I Safe (if p then a else b) Q := by split <;> assumption

elab "fresh_worker_safe_choice" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  let target ← Lean.Meta.withReducible (Lean.Meta.whnf target)
  unless target.isAppOf ``StatePrefixEnsures do Lean.throwError "expected a prefix contract"
  let args := target.getAppArgs
  unless args[args.size - 2]!.isAppOf ``ite do Lean.throwError "expected an explicit choice"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply choice))

private theorem ready_of_preserves (pid : PeerId) (body : WGPrefix Event α)
    (safe : Preserves body) (quiet : StateHistoryFrame admission body) :
    StatePrefixPreserves (Ready pid) Safe body := by
  intro w a h hi
  obtain ⟨suffix,appended,hs,post⟩ := safe w a h hi.1
  refine ⟨suffix,appended,hs,?_⟩
  cases result : (runPrefix (body.run w) a h).1 with
  | error err => trivial
  | ok out =>
    rcases out with ⟨value,b⟩
    have frame := quiet w a h
    rw [appended,List.filterMap_append] at frame
    have noAdmission : suffix.filterMap admission = [] := by simpa using frame
    exact ⟨hs,appended.symm ▸ hi.2.quiet noAdmission⟩

private theorem callback_ready (kind : Kind) (pid : PeerId) (body : WGPrefix Event α)
    (safe : Preserves body) (quiet : StateHistoryFrame admission body) :
    StatePrefixPreserves (Ready pid) Safe (callback id kind pid body) := by
  unfold callback
  refine StatePrefixEnsures.bind
    (StatePrefixEnsures.emit (P := Ready pid) (S := Safe) (Q := fun _ => Ready pid) (.callback kind pid) ?_ ?_) ?_
  · intro h w a hi
    exact hi.1.callback kind pid hi.2
  · intro h w a hi
    exact ⟨hi.1.callback kind pid hi.2,hi.2.quiet rfl⟩
  · intro doneUnit
    exact ready_of_preserves pid body safe quiet

private theorem old_ready (pid : PeerId) (body : WGPrefix Event α)
    (safe : StatePrefixPreserves (Ready pid) Safe body) :
    StatePrefixPreserves (Ready pid) Safe (old id some body) := by
  simpa only [old,List.filterMap_some] using safe.focus id some (fun _ => rfl)

private theorem old_consumer (body : WGPrefix Event (Option PeerId))
    (safe : StatePrefixEnsures Inv Safe body
      (fun result h _ _ => Safe h ∧ ∀ pid, result = some pid → Available h pid)) :
    StatePrefixEnsures Inv Safe (old id some body)
      (fun result h _ _ => Safe h ∧ ∀ pid, result = some pid → Available h pid) := by
  simpa only [old,List.filterMap_some] using safe.focus id some (fun _ => rfl)

theorem responseWith_ready (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, Preserves (session pid))
    (hsq : ∀ pid, StateHistoryFrame admission (session pid))
    (mac : HandshakeMac) (pid : PeerId) :
    StatePrefixPreserves (Ready pid) Safe (responseWith (observedOps id some session keepalive mac) pid) := by
  unfold responseWith
  simp only [observedOps]
  repeat' first
    | (with_reducible apply callback_ready; first | exact hs _ | exact hsq _)
    | with_reducible exact old_ready _ _ (call_ready _ _ _)
    | with_reducible exact lift_ready _ _
    | with_reducible exact pure_ready _ _
    | with_reducible apply chain_ready
    | contradiction
    | split
    | fresh_worker_safe_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only []

abbrev ReadyEnds (pid : PeerId) (g : WGPrefix Event α) :=
  StatePrefixEnsures (Ready pid) Safe g (fun _ => Inv)

private theorem ready_forget (pid : PeerId) (g : WGPrefix Event α)
    (hg : StatePrefixPreserves (Ready pid) Safe g) : ReadyEnds pid g :=
  hg.consequence (fun _ _ _ hi => hi) (fun _ _ _ _ hi => hi.1)

private theorem ready_then (pid : PeerId) (g : WGPrefix Event α) (next : α → WGPrefix Event β)
    (hg : StatePrefixPreserves (Ready pid) Safe g) (hn : ∀ x, ReadyEnds pid (next x)) :
    ReadyEnds pid (g >>= next) := StatePrefixEnsures.bind hg hn

private theorem consumer_then (g : WGPrefix Event (Option PeerId))
    (next : Option PeerId → WGPrefix Event α)
    (hg : StatePrefixEnsures Inv Safe g
      (fun result h _ _ => Safe h ∧ ∀ pid, result = some pid → Available h pid))
    (hn : Preserves (next none)) (hs : ∀ pid, ReadyEnds pid (next (some pid))) :
    Preserves (g >>= next) := by
  apply StatePrefixEnsures.bind hg
  intro result
  cases result with
  | none => exact hn.consequence (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)
  | some pid =>
    apply (hs pid).consequence
    · intro h w a hi; exact ⟨hi.1,hi.2 pid rfl⟩
    · intro x h w a hi; exact hi

private theorem stopped (message : String) (next : α → WGPrefix Event β) :
    Preserves (liftWGPrefix (invariant message) >>= next) := by
  intro w a h hi
  exact ⟨[],by simp only [List.append_nil]; rfl,hi,True.intro⟩

elab "fresh_worker_response_ready" : tactic => do
  let target ← Lean.Meta.withReducible (Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget))
  unless target.isAppOf ``StatePrefixEnsures do Lean.throwError "expected a prefix contract"
  let args := target.getAppArgs
  unless args[args.size - 2]!.isAppOf ``responseWith do Lean.throwError "expected the response sender"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact responseWith_ready _ _ (by assumption) (by assumption) _ _))

theorem afterMac_ready (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, Preserves (session pid)) (hk : ∀ pid, Preserves (keepalive pid))
    (hsq : ∀ pid, StateHistoryFrame admission (session pid))
    (hkq : ∀ pid, StateHistoryFrame admission (keepalive pid))
    (mac : HandshakeMac) (valid : mac.Valid) :
    Preserves (afterMacWith (observedOps id some session keepalive mac) mac.input mac.source mac.loaded mac.checked.value) := by
  unfold afterMacWith
  simp only [observedOps]
  repeat' first
    | with_reducible exact lift _
    | with_reducible exact pure _
    | with_reducible exact stopped _ _
    | with_reducible apply consumer_then _ _ (old_consumer _ (initiation_post mac valid))
    | with_reducible apply consumer_then _ _ (old_consumer _ (response_post mac valid))
    | simp +failIfUnchanged only [pure_bind]
    | with_reducible apply chain
    | with_reducible apply ready_then
    | (with_reducible apply callback_ready; first | exact hs _ | exact hk _ | exact hsq _ | exact hkq _)
    | with_reducible exact old_ready _ _ (call_ready _ _ _)
    | with_reducible exact lift_ready _ _
    | fresh_worker_response_ready
    | with_reducible apply chain_ready
    | with_reducible apply ready_forget
    | with_reducible exact pure_ready _ _
    | contradiction
    | split
    | fresh_worker_safe_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only []

private theorem capture (a : WG.M α) :
    StatePrefixEnsures Inv Safe (captureWGRun a)
      (fun r h _ _ => Safe h ∧ r.Valid a) := by
  apply StatePrefixEnsures.captureWGRun (P := Inv) (S := Safe) a (fun _ _ _ hi => hi)
  intro h w ambient x v b hi run
  exact ⟨hi,run⟩

private theorem pure_run (x : α) (w : WGWorld) (a : Ambient) (h : List Event) :
    runWGPrefix (Pure.pure x) w a h = (.ok ((x,w),a),h) := rfl

private theorem mac_beq_true (a b : MacState) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h

theorem rejected_history (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (mac : HandshakeMac) (msg : Key) (src : SkbSource)
    (loaded : Bool) (state : MacState) (rejected : state ≠ authenticatedMac loaded)
    (w : WGWorld) (a : Ambient) (h : List Event) :
    (runWGPrefix (afterMacWith (observedOps id some session keepalive mac) msg src loaded state) w a h).2 = h := by
  cases loaded <;> cases state <;> try simp_all [authenticatedMac]
  all_goals simp [afterMacWith,observedOps,liftWG_bind_run,WG.orM,WG.andM,
    StateT.run_bind,branch,CounterWindow.branch_run,pure_run,mac_beq_true]
  all_goals by_cases hi : messageType msg = MESSAGE_HANDSHAKE_INITIATION <;>
    by_cases hr : messageType msg = MESSAGE_HANDSHAKE_RESPONSE <;>
    simp_all [liftWG_bind_run,CounterWindow.branch_run,runWGPrefix_lift]
  all_goals rfl

private theorem quiet (g : WGPrefix Event α)
    (frame : ∀ w a h, (runWGPrefix g w a h).2 = h) : Preserves g := by
  intro w a h hi
  have same := frame w a h
  refine ⟨[],?_,?_,?_⟩
  · simpa only [runWGPrefix,runStatePrefix,List.append_nil] using same
  · change Safe (runWGPrefix g w a h).2
    rw [same]
    exact hi
  · cases result : (runPrefix (g.run w) a h).1 with
    | error err => trivial
    | ok out =>
      rcases out with ⟨value,ambient⟩
      change Safe (runWGPrefix g w a h).2
      rw [same]
      exact hi

theorem afterMac_native (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, Preserves (session pid)) (hk : ∀ pid, Preserves (keepalive pid))
    (hsq : ∀ pid, StateHistoryFrame admission (session pid))
    (hkq : ∀ pid, StateHistoryFrame admission (keepalive pid))
    (mac : HandshakeMac)
    (checked : mac.checked.Valid (cookieValidatePacket mac.input mac.source mac.loaded)) :
    Preserves (afterMacWith (observedOps id some session keepalive mac) mac.input mac.source mac.loaded mac.checked.value) := by
  by_cases admitted : mac.checked.value = authenticatedMac mac.loaded
  · exact afterMac_ready session keepalive hs hk hsq hkq mac ⟨checked,admitted⟩
  · apply quiet
    intro w a h
    exact rejected_history session keepalive mac mac.input mac.source mac.loaded mac.checked.value admitted w a h

private theorem given (C : Prop) (g : WGPrefix Event α)
    (hg : C → Preserves g) :
    StatePrefixEnsures (fun h _ _ => Safe h ∧ C) Safe g (fun _ => Inv) := by
  intro w a h hi
  exact hg hi.2 w a h hi.1

theorem receive_preserves (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, Preserves (session pid)) (hk : ∀ pid, Preserves (keepalive pid))
    (hsq : ∀ pid, StateHistoryFrame admission (session pid))
    (hkq : ∀ pid, StateHistoryFrame admission (keepalive pid))
    (msg : Key) (src : SkbSource) : Preserves (observedReceive id some session keepalive msg src) := by
  unfold observedReceive
  apply chain _ _ (lift _)
  intro cookie
  split
  · exact chain _ _ (lift _) (fun _ => pure _)
  · apply chain _ _ (lift _)
    intro loaded
    apply StatePrefixEnsures.bind (capture _)
    intro checked
    exact given _ _ (fun valid => afterMac_native session keepalive hs hk hsq hkq ⟨msg,src,loaded,checked⟩ valid)

/-- Security: the shared native handshake worker retains valid authenticated
roots before every observed peer callback, even if a later action stops. Supplied
session and keepalive observers preserve this property and cannot insert a new
admission between the native consumer and its protected callbacks. -/
theorem observed_preserves (session : PeerId → WGPrefix Event Bool)
    (keepalive : PeerId → WGPrefix Event Unit)
    (hs : ∀ pid, Preserves (session pid)) (hk : ∀ pid, Preserves (keepalive pid))
    (hsq : ∀ pid, StateHistoryFrame admission (session pid))
    (hkq : ∀ pid, StateHistoryFrame admission (keepalive pid)) :
    Preserves (observed id some session keepalive) := by
  unfold observed workerWith
  repeat' first
    | with_reducible exact receive_preserves session keepalive hs hk hsq hkq _ _
    | with_reducible exact lift _
    | with_reducible exact pure _
    | with_reducible apply chain
    | split
    | (session_origin_intro_forall; try dsimp only)


end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFresh.Worker
