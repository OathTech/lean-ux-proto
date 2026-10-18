import Leanux.Proofs.WG.Noise.ResponseCallerSource

/-! Actual whole-response receipts projected through the campaign snapshot.
Normal receipt order and local edges do not assert tag framing between cuts. -/
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ResponseCaller
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- Normal whole-call receipt shape and checked helper effects, with no
caller-frame premise and no claim about tag changes between these cuts. -/
theorem original_response_receipts (pid : PeerId) :
    Campaign2.Ensures (observeProjected pid) (fun _ => True)
      (fun receipts _ => ReceiptShape pid receipts ∧
        ∀ receipt ∈ receipts, ReceiptValid receipt ∧ TagReceiptEffect receipt) := by
  intro g ambient receipts final after pre run
  change (((observeNative pid).run g).run ambient >>= fun ((history, current), inputs) =>
    Except.ok ((history.map Event.receipt, current), inputs)) = _ at run
  cases actual : ((observeNative pid).run g).run ambient with
  | error stop => rw [actual] at run; cases run
  | ok out =>
    obtain ⟨⟨history, current⟩, inputs⟩ := out
    rw [actual] at run
    cases run
    have checked := observeNative_claim pid g ambient history final after pre actual
    refine ⟨checked.1.project, ?_⟩
    intro receipt member
    obtain ⟨event, contained, rfl⟩ := List.mem_map.mp member
    have valid := (checked.2 event contained).1
    exact ⟨⟨event, rfl, valid⟩, Event.receipt_effect valid⟩

/-- Erasure through the Campaign2 observation interface includes every Stop
and every projected successful state. -/
theorem original_response_receipts_erases (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True)
      (do let _ ← observeProjected pid; pure ())
      (sendHandshakeResponse pid) := by
  rw [observeProjected_discard]
  intro g ambient pre
  rfl

end Leanux.Proofs.WG.Noise.ResponseCaller
