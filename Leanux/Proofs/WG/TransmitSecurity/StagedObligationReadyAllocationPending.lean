import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadyAllocation
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationAllocatedPending

/-! The create callback receives the actual allocator's pending batch, not
merely resident cells which might instead be terminal cleanup debts. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.ReadyCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open Staged.Origins AuthenticatedEffects CausalJournal StagedProvenance RetirementSecurity AllocatedObligation

theorem allocate_pending (before : Ready ledger debts locals generation pid peer position history w a)
    (shape : BatchPayload.Shape pid kid peer.staged packets) :
    ∃ (items : List SkbId) (v : WGWorld),
      let receipt : WGRunWitness (List SkbId) := ⟨items,w,v,a,a⟩
      let events := history ++ [Event.old (.allocated packets receipt)]
      let after := assignBatch position history.length ledger
      runWGPrefix (state (Journal.allocate packets)) w a history = (.ok ((items,v),a),events) ∧
      receipt.Valid (packets.mapM newTxSkb) ∧ Step ledger after ∧
      StagedEntry.Inv events after debts (⟨.unpublished,pid,items⟩ :: locals) v ∧
      CreateDisposal.PendingBatch events after items := by
  obtain ⟨items,v,performed,native,step,entry⟩ := allocate before shape
  refine ⟨items,v,performed,native,step,entry,?_⟩
  cases device : w.dev with
  | none => have epoch := before.vacant.1; simp [Packets.epoch,device] at epoch
  | some d =>
    exact allocated_pending_batch before.core.valid packets native device
      (before.toSound.toHeld.allocation_alignment shape)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.ReadyCarrier
