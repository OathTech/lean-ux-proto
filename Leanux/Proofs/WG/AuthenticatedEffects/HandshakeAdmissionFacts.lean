import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeAdmissionSource

/-! Validity of the actual MAC-plus-Noise admission receipts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeAdmissionFacts
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def Safe (h : List HandshakeAdmission) : Prop := ∀ r ∈ h, r.Valid
abbrev Inv (h : List HandshakeAdmission) (_ : WGWorld) (_ : Ambient) := Safe h
abbrev Preserves (g : WGPrefix HandshakeAdmission α) := StatePrefixPreserves Inv Safe g

private theorem lift (a : WG.M α) : Preserves (liftWGPrefix a) :=
  StatePrefixEnsures.lift a (fun _ _ _ hi => hi) (fun _ _ _ _ _ _ hi _ => hi)
private theorem pure (x : α) : Preserves (Pure.pure x) :=
  StatePrefixEnsures.pure x (fun _ _ _ hi => hi) (fun _ _ _ hi => hi)
private theorem append (h : List HandshakeAdmission) (hi : Safe h) (r : HandshakeAdmission)
    (good : r.Valid) : Safe (h ++ [r]) := by
  intro e member
  rcases List.mem_append.mp member with old | fresh
  · exact hi e old
  · simpa using List.mem_singleton.mp fresh ▸ good

private theorem emit_given (r : HandshakeAdmission) (C : Prop) (good : C → r.Valid) :
    StatePrefixEnsures (fun h _ _ => Safe h ∧ C) Safe (emitStatePrefix r) (fun _ => Inv) := by
  apply StatePrefixEnsures.emit
  · intro h w a hi
    exact append h hi.1 r (good hi.2)
  · intro h w a hi
    exact append h hi.1 r (good hi.2)

private theorem capture (a : WG.M α) :
    StatePrefixEnsures Inv Safe (captureWGRun a)
      (fun r h _ _ => Safe h ∧ r.Valid a) := by
  apply StatePrefixEnsures.captureWGRun (P := Inv) (S := Safe) a (fun _ _ _ hi => hi)
  intro h w ambient x v b hi run
  exact ⟨hi,run⟩

private theorem chain {α β : Type} (g : WGPrefix HandshakeAdmission α)
    (tail : α → WGPrefix HandshakeAdmission β) (hg : Preserves g)
    (ht : ∀ x, Preserves (tail x)) : Preserves (g >>= tail) :=
  StatePrefixEnsures.bind hg ht

private theorem choice (p : Prop) [Decidable p] (a b : WGPrefix HandshakeAdmission α)
    (ha : Preserves a) (hb : Preserves b) : Preserves (if p then a else b) := by
  split <;> assumption

theorem initiation (mac : HandshakeMac) (valid : mac.Valid) : Preserves (admitInitiation mac) := by
  unfold admitInitiation
  apply StatePrefixEnsures.bind (capture _)
  intro checked
  by_cases accepted : checked.value.isSome = true
  · simp only [accepted,↓reduceIte]
    exact StatePrefixEnsures.bind
      (emit_given (.initiation mac checked) _ (fun authenticated => ⟨valid,authenticated,accepted⟩))
      (fun _ => lift _)
  · simp only [accepted]
    exact (lift _).consequence (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)

theorem response (mac : HandshakeMac) (valid : mac.Valid) : Preserves (admitResponse mac) := by
  unfold admitResponse
  apply StatePrefixEnsures.bind (capture _)
  intro checked
  by_cases accepted : checked.value.isSome = true
  · simp only [accepted,↓reduceIte]
    exact StatePrefixEnsures.bind
      (emit_given (.response mac checked) _ (fun authenticated => ⟨valid,authenticated,accepted⟩))
      (fun _ => lift _)
  · simp only [accepted]
    exact (lift _).consequence (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)

elab "admission_safe_choice" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``Preserves do Lean.throwError "expected a preservation contract"
  let observed := target.getAppArgs.back!
  unless observed.isAppOf ``ite do Lean.throwError "expected an explicit choice"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply choice))

theorem responseWith_preserves (mac : HandshakeMac) (pid : PeerId) :
    Preserves (responseWith (admissionOps mac) pid) := by
  unfold responseWith
  simp only [admissionOps]
  repeat' first
    | with_reducible exact lift _
    | with_reducible exact pure _
    | with_reducible apply chain
    | split
    | admission_safe_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only [Option.some.injEq]

elab "admission_response_safe" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isAppOf ``Preserves do Lean.throwError "expected a preservation contract"
  let observed := target.getAppArgs.back!
  unless observed.isAppOf ``responseWith do Lean.throwError "expected the response sender"
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact responseWith_preserves _ _))

theorem afterMac_preserves (mac : HandshakeMac) (valid : mac.Valid) :
    Preserves (afterMacWith (admissionOps mac) mac.input mac.source mac.loaded mac.checked.value) := by
  unfold afterMacWith
  simp only [admissionOps]
  repeat' first
    | admission_response_safe
    | with_reducible exact initiation mac valid
    | with_reducible exact response mac valid
    | with_reducible exact lift _
    | with_reducible exact pure _
    | with_reducible apply chain
    | split
    | admission_safe_choice
    | (session_origin_intro_forall; try dsimp only)
    | simp +failIfUnchanged only [bind_assoc,pure_bind]
  all_goals try simp_all only [Option.some.injEq]

private theorem pure_run (x : α) (w : WGWorld) (a : Ambient) (h : List HandshakeAdmission) :
    runWGPrefix (Pure.pure x) w a h = (.ok ((x,w),a),h) := rfl

private theorem mac_beq_true (a b : MacState) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h

theorem rejected_history (mac : HandshakeMac) (msg : Key) (src : SkbSource)
    (loaded : Bool) (state : MacState) (rejected : state ≠ authenticatedMac loaded)
    (w : WGWorld) (a : Ambient) (h : List HandshakeAdmission) :
    (runWGPrefix (afterMacWith (admissionOps mac) msg src loaded state) w a h).2 = h := by
  cases loaded <;> cases state <;> try simp_all [authenticatedMac]
  all_goals simp [afterMacWith,admissionOps,liftWG_bind_run,WG.orM,WG.andM,
    StateT.run_bind,branch,CounterWindow.branch_run,pure_run,mac_beq_true]
  all_goals by_cases hi : messageType msg = MESSAGE_HANDSHAKE_INITIATION <;>
    by_cases hr : messageType msg = MESSAGE_HANDSHAKE_RESPONSE <;>
    simp_all [liftWG_bind_run,CounterWindow.branch_run,runWGPrefix_lift]
  all_goals rfl

private theorem quiet (g : WGPrefix HandshakeAdmission α)
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
    Preserves (afterMacWith (admissionOps mac) mac.input mac.source mac.loaded mac.checked.value) := by
  by_cases admitted : mac.checked.value = authenticatedMac mac.loaded
  · exact afterMac_preserves mac ⟨checked,admitted⟩
  · apply quiet
    intro w a h
    exact rejected_history mac mac.input mac.source mac.loaded mac.checked.value admitted w a h

private theorem given (C : Prop) (g : WGPrefix HandshakeAdmission α)
    (hg : C → Preserves g) :
    StatePrefixEnsures (fun h _ _ => Safe h ∧ C) Safe g (fun _ => Inv) := by
  intro w a h hi
  exact hg hi.2 w a h hi.1

theorem receive (msg : Key) (src : SkbSource) : Preserves (receiveAdmissions msg src) := by
  unfold receiveAdmissions
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
    (h : List HandshakeAdmission) (safe : Safe h) :
    ∃ suffix, (runWGPrefix (receiveAdmissions msg src) w a h).2 = h ++ suffix ∧
      Safe (h ++ suffix) := by
  obtain ⟨suffix,history,valid,_⟩ := receive msg src w a h safe
  exact ⟨suffix,history,history ▸ valid⟩

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeAdmissionFacts
