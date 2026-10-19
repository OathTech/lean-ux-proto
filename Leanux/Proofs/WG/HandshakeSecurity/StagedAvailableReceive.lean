import Leanux.Proofs.WG.HandshakeSecurity.StagedAvailableWorkers
import Leanux.Proofs.WG.TransmitSecurity.StagedReceiveFrames

/-! Receive metadata and accepted-packet finish paths preserve available staged
credits. Any following staged send remains an explicit caller callback. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem fresh_receive (pid : PeerId) : Preserves (Inv h) (keepKeyFreshRx pid) := by
  unfold keepKeyFreshRx
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued _ _)
    | staged_available_native

theorem stats (pid : PeerId) (len : Nat) : Preserves (Inv h) (updateRxStats pid len) := by
  unfold updateRxStats
  repeat' staged_available_native

theorem dishonest (why : Dishonest) : Preserves (Inv h) (WG.dishonest why) := by
  cases why <;> unfold WG.dishonest <;> apply modify_device <;> intro d <;> rfl

theorem prepare (pid : PeerId) (packet : RxPacket) : Preserves (Inv h) (RxCredits.prepareRest pid packet) := by
  unfold RxCredits.prepareRest
  repeat' first
    | (rx_retention_head keepKeyFreshRx; exact fresh_receive _)
    | (rx_retention_head timersTraversal; exact traversal _)
    | (rx_retention_head timersDataReceived; exact data_received _)
    | (rx_retention_head updateRxStats; exact stats _ _)
    | (rx_retention_head WG.dishonest; exact dishonest _)
    | (rx_retention_head inetEcnDecapsulate; exact store (inetEcnDecapsulate_sameWGStore _ _ _))
    | staged_available_native

theorem lookup_repay (protocol : Nat) (bytes : List UInt8) :
    Preserves (Inv h) (RxBorrow.source protocol bytes) := by
  apply frame
  · exact (RxBorrow.source_frame protocol bytes).of_factor
      (fun obs => obs.1.dev.map Device.ifindex) Packets.epoch (fun w => by
        simp only [PeerBorrow.view,PeerBorrow.outsidePeers,wgStoreView,Packets.epoch,
          Option.map_map,Function.comp_def])
  · apply Staged.of_view
    exact (RxBorrow.source_frame protocol bytes).of_factor
      (fun obs pid => (obs.2 pid).map (fun p => (p.internalId,p.staged))) stagedAt (fun _ => rfl)

theorem receive_finish (pid : PeerId) (ready : Packets.RxReady) :
    Preserves (Inv h) (Packets.rxFinish pid ready) := by
  rw [← RxCredits.rxFinishSource_eq]
  unfold RxCredits.rxFinishSource
  repeat' first
    | (rx_retention_head RxBorrow.source; exact lookup_repay _ _)
    | (rx_retention_head WG.dishonest; exact dishonest _)
    | (rx_retention_head updateRxStats; exact stats _ _)
    | staged_available_native

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability.Native
