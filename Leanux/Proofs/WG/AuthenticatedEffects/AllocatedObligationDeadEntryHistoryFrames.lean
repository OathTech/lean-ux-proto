import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationDeadEntrySource

/-! History extension of the original DEAD repayment suffix retains the
actual key accesses and nested release receipts even on Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.DeadEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

theorem repay_appends (pid : PeerId) (key : KeypairId) : Appends (repay pid key) := by
  unfold repay
  apply Appends.bind (show Appends (Admission.actualOps.access (keypairPutPrefix (some key) false)) from
    Appends.focus _ _ _)
  intro _
  apply Appends.bind (CausalJournal.CallbackQuiet.release (fun _ => (none : Option Unit))
    (fun _ => rfl) (fun _ => rfl) (some pid)).1
  intro _
  exact Appends.pure _

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.DeadEntry
