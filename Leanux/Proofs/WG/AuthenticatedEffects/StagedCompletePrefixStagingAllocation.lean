import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingRestore
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAllocation

/-! The actual batch allocator appends one native receipt. Its successor
retains the exact ticket ordinal assignment and unpublished packet ownership. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompleteCarrier AllocatedObligation

def Allocated (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (position : Nat) (pid : PeerId) (packets : List DataPacket)
    (items : List SkbId) (history : List Event) (w : WGWorld) (a : Ambient) : Prop :=
  ∃ before receipt, history=before++[Event.old (.allocated packets receipt)] ∧
    receipt.value=items ∧ receipt.after=w ∧ receipt.ambientAfter=a ∧
    receipt.Valid (packets.mapM newTxSkb) ∧
    Staged.Obligations.Step ledger (assignBatch position before.length ledger) ∧
    Accounted history (assignBatch position before.length ledger) debts (⟨.unpublished,pid,items⟩::locals) w ∧
    CreateDisposal.PendingBatch history (assignBatch position before.length ledger) items

/-- No successful-allocation premise is assumed. The source's total allocator
provides its own receipt and exact successor, then certifies the single new
prefix using that same accounted unpublished batch. -/
theorem allocate (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (kid : KeypairId) (packets : List DataPacket) :
    StateEnsures (fun h w a=>CompleteSelected.Ready ledger debts locals generation pid peer position h w a ∧
      BatchPayload.Shape pid kid peer.staged packets) CompleteProduct.Safe
      (state (Journal.allocate packets)) (Allocated ledger debts locals position pid packets) := by
  intro w a h before
  obtain ⟨items,v,performed,native,step,accounted,pending⟩ :=
    CompleteSelected.allocate before.1.1 before.1.2
  let receipt : WGRunWitness (List SkbId) := ⟨items,w,v,a,a⟩
  let event := Event.old (.allocated packets receipt)
  have safe : CompleteProduct.Safe (h++[event]) :=
    ⟨debts,.accounted _ _ _ v accounted⟩
  have all := before.2.append (Cuts.singleton before.2.last safe)
  change runPrefix ((state (Journal.allocate packets)).run w) a h=_ at performed
  rw [performed]
  exact ⟨[event],rfl,all,⟨h,receipt,rfl,rfl,rfl,rfl,native,step,accounted,pending⟩,all⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
