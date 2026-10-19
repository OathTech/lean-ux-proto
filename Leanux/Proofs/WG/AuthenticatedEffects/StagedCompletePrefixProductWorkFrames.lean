import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductWorkNative
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductSource

/-! Native selector and clear-queue frames used by the all-prefix worker
composition. These retain the same packet and allocation projections. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.WorkFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Queues.RxCredits CompleteProduct

theorem send_select : Checked (liftPrefix SendWorkCauses.select) := by
  apply store
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w pid v run
  exact congrArg wgStoreView (SendWorkCauses.select_member w v pid run).1

theorem clear_dequeue (pid : PeerId) : Checked
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

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.WorkFrames
