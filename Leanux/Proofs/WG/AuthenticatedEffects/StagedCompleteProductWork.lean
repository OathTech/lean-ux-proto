import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductWorkNative
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductSource

/-! Scheduled send and clear preserve both directions of packet accounting
and native allocation. The clear callback retains its actual peer-release
settlement; only the scheduler's selector and queue bookkeeping are passive. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Queues.RxCredits

private theorem send_state (pid : PeerId) : StateChecked (CausalJournal.flushedSend pid) :=
  pair (CompleteSend.flushed Safe account_safe pid) (WorkNative.send_erases pid) (WorkNative.send_allocated pid)

private theorem clear_state (pid : PeerId) :
    StateChecked (NestedPeerRelease.clearWith (Driver.nestedOps hooks) pid) :=
  pair (CompleteClear.clear Safe account_safe pid) (WorkNative.clear_erases pid) (WorkNative.clear_allocated pid)

private theorem send_select : Checked (liftPrefix SendWorkCauses.select) := by
  apply store
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w pid v run
  exact congrArg wgStoreView (SendWorkCauses.select_member w v pid run).1

private theorem clear_dequeue (pid : PeerId) : Checked
    (liftPrefix (liftWG (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}))) := by
  apply wg
  apply CompleteAllocated.native Safe account_safe
  intro history ledger
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  cases run
  have entryView : StagedEntry.view {w with dev := w.dev.map (fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})} =
      StagedEntry.view w := by
    unfold StagedEntry.view Packets.epoch Staged.stagedAt PacketMaterial.view
      Packets.snapshot Packets.deviceStore TxDisposition.txPackets txQueueContents handoffTxView
    cases w.dev <;> rfl
  refine ⟨before.1.same_view entryView,?_⟩
  obtain ⟨past,allocated⟩ := before.2
  refine ⟨past,allocated.congr ?_ ?_⟩
  · unfold identityView Peers.snapshot keypairResidents packetResidents
    cases device : w.dev <;> simp [device]
  · cases device : w.dev <;>
      simp [allocationMetadata,deviceAllocationMetadata,device]

theorem scheduled_send : Checked (Driver.sendWorkerObserved hooks) := by
  change Checked (HandshakeSecurity.SendExchange.oneWith liftPrefix
    (fun pid => liftWGObserver (CausalJournal.flushedSend pid)))
  exact bind_checked send_select (fun pid => state (send_state pid))

theorem scheduled_clear : Checked (Driver.clearWorkerObserved hooks) := by
  unfold Driver.clearWorkerObserved NestedPeerRelease.oneClearWith
  repeat' first
    | (complete_product_head runWorkerPrefix
       apply runWorkerPrefix_preserves carrier_safe stable
       exact state (clear_state _))
    | (complete_product_native liftWG
       first
       | exact product_store _ (liftWG_sameProductStore _ getDev_sameWGStore)
       | exact clear_dequeue _)
    | (complete_product_native invariant; exact ambient _)
    | (complete_product_native peekUnit; exact ambient _)
    | (complete_product_native resolveUnit; exact ambient _)
    | complete_product_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct
