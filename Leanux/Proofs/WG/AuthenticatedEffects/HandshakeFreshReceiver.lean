import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFreshConsumers

/-! Receiver callbacks inherit the admission produced by their native consumer. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFresh
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources HandshakeCausal
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

elab "fresh_safe_choice" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  let target ← Lean.Meta.withReducible (Lean.Meta.whnf target)
  unless target.isAppOf ``StatePrefixEnsures do Lean.throwError "expected a prefix contract"
  let args := target.getAppArgs
  unless args[args.size - 2]!.isAppOf ``ite do Lean.throwError "expected an explicit choice"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply choice))

theorem responseWith_ready (mac : HandshakeMac) (pid : PeerId) :
    StatePrefixPreserves (Ready pid) Safe (responseWith (ops mac) pid) := by
  unfold responseWith
  simp only [ops]
  repeat' first
    | with_reducible exact call_ready _ _ _
    | with_reducible exact lift_ready _ _
    | with_reducible exact pure_ready _ _
    | with_reducible apply chain_ready
    | contradiction
    | split
    | fresh_safe_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only [Option.some.injEq]

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

elab "fresh_response_ready" : tactic => do
  let target ← Lean.Meta.withReducible (Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget))
  unless target.isAppOf ``StatePrefixEnsures do Lean.throwError "expected a prefix contract"
  let args := target.getAppArgs
  unless args[args.size - 2]!.isAppOf ``responseWith do Lean.throwError "expected the response sender"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact responseWith_ready _ _))

theorem afterMac_ready (mac : HandshakeMac) (valid : mac.Valid) :
    Preserves (afterMacWith (ops mac) mac.input mac.source mac.loaded mac.checked.value) := by
  unfold afterMacWith
  simp only [ops]
  repeat' first
    | with_reducible exact lift _
    | with_reducible exact pure _
    | with_reducible exact stopped _ _
    | with_reducible apply consumer_then _ _ (initiation_post mac valid)
    | with_reducible apply consumer_then _ _ (response_post mac valid)
    | simp +failIfUnchanged only [pure_bind]
    | with_reducible apply chain
    | with_reducible apply ready_then
    | with_reducible exact call_ready _ _ _
    | with_reducible exact lift_ready _ _
    | fresh_response_ready
    | with_reducible apply chain_ready
    | with_reducible apply ready_forget
    | with_reducible exact pure_ready _ _
    | contradiction
    | split
    | fresh_safe_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only [Option.some.injEq]

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

theorem rejected_history (mac : HandshakeMac) (msg : Key) (src : SkbSource)
    (loaded : Bool) (state : MacState) (rejected : state ≠ authenticatedMac loaded)
    (w : WGWorld) (a : Ambient) (h : List Event) :
    (runWGPrefix (afterMacWith (ops mac) msg src loaded state) w a h).2 = h := by
  cases loaded <;> cases state <;> try simp_all [authenticatedMac]
  all_goals simp [afterMacWith,ops,liftWG_bind_run,WG.orM,WG.andM,
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

theorem afterMac_native (mac : HandshakeMac)
    (checked : mac.checked.Valid (cookieValidatePacket mac.input mac.source mac.loaded)) :
    Preserves (afterMacWith (ops mac) mac.input mac.source mac.loaded mac.checked.value) := by
  by_cases admitted : mac.checked.value = authenticatedMac mac.loaded
  · exact afterMac_ready mac ⟨checked,admitted⟩
  · apply quiet
    intro w a h
    exact rejected_history mac mac.input mac.source mac.loaded mac.checked.value admitted w a h

private theorem given (C : Prop) (g : WGPrefix Event α)
    (hg : C → Preserves g) :
    StatePrefixEnsures (fun h _ _ => Safe h ∧ C) Safe g (fun _ => Inv) := by
  intro w a h hi
  exact hg hi.2 w a h hi.1

theorem receive_preserves (msg : Key) (src : SkbSource) : Preserves (HandshakeCausal.receive msg src) := by
  unfold HandshakeCausal.receive
  apply chain _ _ (lift _)
  intro cookie
  split
  · exact chain _ _ (lift _) (fun _ => pure _)
  · apply chain _ _ (lift _)
    intro loaded
    apply StatePrefixEnsures.bind (capture _)
    intro checked
    exact given _ _ (fun valid => afterMac_native ⟨msg,src,loaded,checked⟩ valid)

theorem receipts (msg : Key) (src : SkbSource) (w : WGWorld) (a : Ambient)
    (h : List Event) (safe : Safe h) :
    ∃ suffix, (runWGPrefix (HandshakeCausal.receive msg src) w a h).2 = h ++ suffix ∧
      Safe (h ++ suffix) := by
  obtain ⟨suffix,history,valid,_⟩ := receive_preserves msg src w a h safe
  exact ⟨suffix,history,history ▸ valid⟩


/-- Every callback in this actual receiver invocation uses its newest native
admission, with no intervening admission for another packet or peer. -/
theorem callback_fresh (msg : Key) (src : SkbSource) (w : WGWorld) (a : Ambient)
    (history : List Event) (safe : Safe history)
    (before after : List Event) (kind : Kind) (pid : PeerId)
    (position : (runWGPrefix (HandshakeCausal.receive msg src) w a history).2 =
      before ++ .callback kind pid :: after) : Available before pid :=
  (receive_preserves msg src w a history safe).choose_spec.2.1 before (.callback kind pid) after position

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFresh
