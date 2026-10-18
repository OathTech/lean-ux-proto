import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationAuthorizationSource

namespace Leanux.Proofs.WG.HandshakeSecurity.Confirmation.Authorization
open Leanux Leanux.WG Leanux.Proofs.Logged

def Valid (h : List Receipt) : Prop := ∀ r ∈ h, r.Valid

private theorem silent {α : Type} (action : WG.M α) :
    StatePrefixPreserves (fun h _ _ => Valid h) Valid (liftWGPrefix action : WGPrefix Receipt α) :=
  StatePrefixEnsures.lift _ (fun _ _ _ hi => hi) (fun _ _ _ _ _ _ hi _ => hi)

private theorem pure_safe {α : Type} (x : α) :
    StatePrefixPreserves (fun h _ _ => Valid h) Valid (pure x : WGPrefix Receipt α) :=
  StatePrefixEnsures.pure _ (fun _ _ _ hi => hi) (fun _ _ _ hi => hi)

private theorem branch_safe {α : Type} (decision : Decision) (value : Bool)
    (f : Bool → WGPrefix Receipt α)
    (hf : StatePrefixPreserves (fun h _ _ => Valid h) Valid (f value)) :
    StatePrefixPreserves (fun h _ _ => Valid h) Valid
      (liftWGPrefix (branch decision value) >>= f) := by
  have tested : StatePrefixEnsures (fun h _ _ => Valid h) Valid
      (liftWGPrefix (branch decision value) : WGPrefix Receipt Bool)
      (fun returned h _ _ => returned = value ∧ Valid h) := by
    apply StatePrefixEnsures.lift (P := fun h _ _ => Valid h) (S := Valid)
      _ (fun _ _ _ hi => hi)
    intro h w a returned v b hi run
    have source : ((branch decision value : WG.M Bool).run w).run a =
        .ok ((value, w), CounterWindow.record a decision value) := rfl
    rw [source] at run
    cases run
    exact ⟨rfl, hi⟩
  apply StatePrefixEnsures.bind tested
  intro returned w a h hi
  rcases hi with ⟨rfl, hi⟩
  exact hf w a h hi

theorem consume_valid (counter : WGRunWitness Bool) (pid : PeerId) (pkt : RxPacket) (ep : Endpoint)
    (checked : counter.Valid (counterValidate pkt.keypair pkt.nonce))
    (accepted : counter.value = true) (crypted : pkt.state = .crypted) :
    StatePrefixPreserves (fun h _ _ => Valid h) Valid (consumeObserved counter pid pkt ep) := by
  unfold consumeObserved
  apply StatePrefixEnsures.bind (silent _)
  intro _
  have confirm : StatePrefixPreserves (fun h _ _ => Valid h) Valid
      (receiptWGObserved (liftWGPrefix (receivedWithKeypair pid pkt.keypair))
        (fun execution => (⟨counter, ⟨pid, pkt, ep, execution⟩⟩ : Receipt))) := by
    intro w a h hi
    have equation := runWGPrefix_receiptWGObserved (liftWGPrefix (receivedWithKeypair pid pkt.keypair))
      (fun execution => (⟨counter, ⟨pid, pkt, ep, execution⟩⟩ : Receipt)) w a h
    rw [runWGPrefix_lift] at equation
    change runStatePrefix _ w a h = _ at equation
    unfold runStatePrefix at equation
    rw [equation]
    cases run : ((receivedWithKeypair pid pkt.keypair).run w).run a with
    | error stop => exact ⟨[], by simp, hi, trivial⟩
    | ok out =>
      rcases out with ⟨⟨confirmed, v⟩, b⟩
      have valid : Valid (h ++ [⟨counter, ⟨pid, pkt, ep, ⟨confirmed, w, v, a, b⟩⟩⟩]) := by
        intro r member
        rcases List.mem_append.mp member with old | last
        · exact hi r old
        · have equal := List.mem_singleton.mp last
          subst r
          exact ⟨checked, accepted, crypted, run⟩
      exact ⟨_, rfl, valid, valid⟩
  exact StatePrefixEnsures.bind confirm (fun _ => silent _)

theorem afterCounter_valid (counter : WGRunWitness Bool) (pid : PeerId) (pkt : RxPacket)
    (checked : counter.Valid (counterValidate pkt.keypair pkt.nonce))
    (crypted : pkt.state = .crypted) :
    StatePrefixPreserves (fun h _ _ => Valid h) Valid (afterCounter counter pid pkt) := by
  unfold afterCounter
  apply branch_safe
  cases accepted : counter.value with
  | false => exact pure_safe _
  | true =>
    apply StatePrefixEnsures.bind (silent (endpointFromSkb pkt.source))
    intro endpoint
    apply branch_safe
    cases endpoint with
    | none => exact pure_safe _
    | some ep =>
      exact StatePrefixEnsures.bind (consume_valid counter pid pkt ep checked accepted crypted)
        (fun _ => pure_safe _)

theorem eligible_valid (pid : PeerId) (pkt : RxPacket) :
    StatePrefixPreserves (fun h _ _ => Valid h) Valid (eligibleObserved pid pkt) := by
  unfold eligibleObserved
  apply branch_safe
  by_cases crypted : pkt.state = .crypted
  · simp only [crypted]
    have captured : StatePrefixEnsures (fun h _ _ => Valid h) Valid
        (captureWGRun (counterValidate pkt.keypair pkt.nonce) : WGPrefix Receipt (WGRunWitness Bool))
        (fun r h _ _ => r.Valid (counterValidate pkt.keypair pkt.nonce) ∧ Valid h) := by
      apply StatePrefixEnsures.captureWGRun (P := fun h _ _ => Valid h) (S := Valid)
        _ (fun _ _ _ hi => hi)
      intro h w a value v b hi run
      exact ⟨run, hi⟩
    apply StatePrefixEnsures.bind captured
    intro counter w a h hi
    exact afterCounter_valid counter pid pkt hi.1 crypted w a h hi.2
  · have different : (pkt.state != PacketState.crypted) = true := by
      cases state : pkt.state <;> first | rfl | exact (crypted state).elim
    simp only [different, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact pure_safe _

end Leanux.Proofs.WG.HandshakeSecurity.Confirmation.Authorization
