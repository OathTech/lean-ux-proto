import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAdmissionQueueFrames

/-! A queue-publication Stop tied back to the actual create admission input.
The entry anchor of the surrounding initialized driver remains separate;
this source interval never replaces it with an existential accounted world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation

/-- At a stopped installed queue, the original admission prefix reaches
the same queued ownership cut. The later failed ring tail is retained as
an actual run from that cut, with the original fixed ledger and debts. -/
theorem admission_queue_stopped_cut
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg)
    (read : runPrefix (Admission.actualOps.access (getPeerMixed pid)) w history = (.ok (peer,u),readHistory))
    (guarded : runPrefix (Admission.actualOps.step (branch .createDataDead peer.isDead)) u readHistory =
      (.ok (false,q),readHistory))
    (frontier : Queue.EnqueueFrontier ledger debts locals pid items q readHistory reason last) :
    (runPrefix (QueueHandoff.focused (QueueHandoff.before pid items)) q readHistory = (.error reason,last)) ∨
    ∃ cut cutHistory,
      QueuedPath ledger debts locals pid items q readHistory cut cutHistory ∧
      runPrefix (admissionInstallPrefix pid items) w history = (.ok (some true,cut),cutHistory) ∧
      Accounted cutHistory ledger debts locals cut.wg ∧
      runPrefix (QueueHandoff.focused (QueueHandoff.after items)) cut cutHistory = (.error reason,last) := by
  have entry := admission_queue_entry before read guarded
  cases queue_stop_of_frontier entry frontier with
  | beforeWrite _ failed => exact Or.inl failed
  | afterWrite cut cutHistory path failed =>
    exact Or.inr ⟨cut,cutHistory,path,admission_install_prefix_run read guarded path.run,path.accounted,failed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
