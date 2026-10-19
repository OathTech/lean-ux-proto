import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductTx
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSendWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteClearWorker

/-! Native allocation companions for the actual send and clear callbacks.
The independently established complete-history contracts remain necessary. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.WorkNative
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity

theorem send_erases (pid : PeerId) :
    ErasesStatePrefix (CausalJournal.flushedSend pid) (runFlushedSendWork pid) := by
  intro w a h
  have projected := congrArg Prod.fst (CausalJournal.flushed_projects pid w a h)
  change ((runFlushedSendWork pid).run w).run a =
    (runPrefix ((CausalJournal.flushedSend pid).run w) a h).1.map id at projected
  simpa only [Except.map_id,id_eq] using projected.symm

theorem send_allocated (pid : PeerId) : Preserves StackOwnership.Allocated (runFlushedSendWork pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact Allocated.native (runFlushedSendWorkPrefix_erases pid)
    (runFlushedSendWorkPrefix_preserves allocationAmbient allocationPeerRemoval pid) before a b run

theorem clear_erases (pid : PeerId) : ErasesStatePrefix
    (NestedPeerRelease.clearWith (Driver.nestedOps CausalJournal.hooks) pid) (queuedExpiredZeroKeyMaterial pid) := by
  change ErasesStatePrefix (NestedPeerRelease.clearWith
    (NestedPeerRelease.observedOps CausalJournal.Event.stagedDisposal CausalJournal.stagedDisposal?) pid) _
  simpa only [NestedPeerRelease.clear_native] using NestedPeerRelease.clear_erases
    (NestedPeerRelease.observedOps_erases CausalJournal.Event.stagedDisposal CausalJournal.stagedDisposal?) pid

theorem clear_allocated (pid : PeerId) : Preserves StackOwnership.Allocated (queuedExpiredZeroKeyMaterial pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact Allocated.native (queuedExpiredZeroKeyMaterialPrefix_erases pid)
    (queuedExpiredZeroKeyMaterialPrefix_preserves allocationAmbient
      allocationPeerRemoval.indexRemove allocationPeerRemoval.keypairPut pid) before a b run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.WorkNative
