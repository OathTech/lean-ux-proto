import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSelected
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocationFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadyAllocationPending

/-! Actual total batch allocation produces one unpublished owner, its pending
ticket batch, and both accounting directions on the exact ordinal assignment. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal StagedTerminalComplete CompleteCarrier

theorem allocate (before : Ready ledger debts locals generation pid peer position history w a)
    (shape : BatchPayload.Shape pid kid peer.staged packets) :
    ∃ (items : List SkbId) (v : WGWorld),
      let receipt : WGRunWitness (List SkbId) := ⟨items,w,v,a,a⟩
      let events := history ++ [Event.old (.allocated packets receipt)]
      let after := assignBatch position history.length ledger
      runWGPrefix (state (Journal.allocate packets)) w a history = (.ok ((items,v),a),events) ∧
      receipt.Valid (packets.mapM newTxSkb) ∧ Staged.Obligations.Step ledger after ∧
      Accounted events after debts (⟨.unpublished,pid,items⟩ :: locals) v ∧
      CreateDisposal.PendingBatch events after items := by
  obtain ⟨items,v,performed,native,step,entry,pending⟩ := ReadyCarrier.allocate_pending before.toReady shape
  refine ⟨items,v,performed,native,step,⟨entry,?_⟩,pending⟩
  exact (before.complete.assigned position history.length).append_quiet
    (fun _ member => by cases List.mem_singleton.mp member; intro pos; rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
