import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetired
import Leanux.Proofs.WG.Lifetimes.DeviceCreation

/-! Creation changes the device epoch only after the original absent-device
guard. Empty replacement geometry preserves already-terminal history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteDeviceCreation
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open Queues.RxCredits
set_option maxHeartbeats 600000

theorem link_entry (w : WGWorld) :
    StagedEntry.view {dev := (linkView w).dev} = StagedEntry.view w := by
  cases device : w.dev <;>
    simp [funext_iff,StagedEntry.view,linkView,linkStore,linkDevice,wgStoreView,
      Packets.epoch,Staged.stagedAt,PacketMaterial.view,TxDisposition.txPackets,
      Packets.snapshot,Packets.deviceStore,txQueueContents,handoffTxView,device]

theorem link_frame (same : linkView v = linkView w) : StagedEntry.view v = StagedEntry.view w := by
  have projected := congrArg (fun s : WGStoreView => StagedEntry.view {dev := s.dev}) same
  simpa only [link_entry] using projected

theorem fresh_staged (epoch pid stamp : Nat) :
    stagedPackets epoch pid stamp (freshDeviceWorld w) = [] := by
  simp [stagedPackets,Staged.stagedAt,freshDeviceWorld]

theorem fresh_cells : TxDisposition.txPackets (freshDeviceWorld w) = fun _ => none := by
  funext id
  simp [TxDisposition.txPackets,freshDeviceWorld]

theorem fresh_coverage : TxCoverage [] (freshDeviceWorld w) := by
  intro id packet found
  simp [fresh_cells] at found

theorem fresh_inventory : TxInventory [] (freshDeviceWorld w) := by
  constructor
  · simp [txLocalItems]
  · intro pid p found
    simp [peerAt,freshDeviceWorld] at found
  · intro pid p other q found
    simp [peerAt,freshDeviceWorld] at found
  · intro pid p found
    simp [peerAt,freshDeviceWorld] at found
  · intro id member
    simp [txLocalItems] at member
  · intro pid p found
    simp [peerAt,freshDeviceWorld] at found

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteDeviceCreation
