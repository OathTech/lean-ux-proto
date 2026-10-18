import Leanux.Proofs.WG.Noise.ReceiveStepCallerFrames

/-! Actual queue selection and reception receipts for one native receive step. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ReceiveStepCaller
open Leanux Leanux.WG Leanux.Proofs.WG.Origins
open ReceptionCaller
theorem original_receiveStep_receipt (entry : Campaign2.Snapshot) :
    Campaign2.Ensures observeStep (fun s => s = entry)
      (fun r _ => r.entry = entry ∧ PollShape r.entry r.poll) := by
  intro g ambient r final after pre run
  change observeStepAt (Campaign2.snapshot g ambient) g ambient = _ at run
  obtain ⟨same,shape⟩ := observeStepAt_shape g ambient r final after run
  exact ⟨same.trans pre,shape⟩

theorem original_receiveStep_receipt_erases :
    Campaign2.AgreesOn (fun _ => True)
      (do let r ← observeStep; pure r.poll.value) receiveStep := by
  rw [observeStep_discard]
  intro g ambient _
  rfl


end Leanux.Proofs.WG.Noise.ReceiveStepCaller
