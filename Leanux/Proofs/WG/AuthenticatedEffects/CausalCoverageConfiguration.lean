import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageFixture
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageSend

/-! Configuration and lifecycle callbacks restore scopes even when they drain
queued handshake work. Only the exact guarded fixture sites enter local roots. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues Configuration
open HandshakeSecurity.SendExchange
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem send_drain (upTo : Option PeerId) : StateAt frames (Driver.sendDrainObserved hooks upTo) := by
  unfold Driver.sendDrainObserved drainWith
  repeat' first
    | (coverage_head Driver.Hooks.flushedSend; exact flushed_send _)
    | (coverage_head Driver.Hooks.peerRelease; exact state_lift _)
    | coverage_state_step

theorem remove_after (pid : PeerId) : StateAt frames (afterDeadWith liftWGPrefix (Driver.sendDrainObserved hooks) pid) := by
  unfold afterDeadWith timersStopWith
  repeat' first
    | (coverage_head Driver.sendDrainObserved; exact send_drain _)
    | (coverage_head Driver.Hooks.peerRelease; exact state_lift _)
    | coverage_state_step

theorem remove (peer : Option PeerId) : StateAt frames (Driver.removeObserved hooks peer) := by
  unfold Driver.removeObserved
  rw [show hooks.peerRelease = (fun peer => liftWGPrefix (peerPut peer)) from rfl,
    HandshakeSecurity.StagedDisposal.Lifecycle.remove_neutral]
  unfold removeWith peerRemoveWith
  repeat' first
    | (coverage_head afterDeadWith; exact remove_after _)
    | (coverage_head Driver.Hooks.peerRelease; exact state_lift _)
    | coverage_state_step

theorem remove_all : StateAt frames (Driver.removeAllObserved hooks) := by
  unfold Driver.removeAllObserved
  rw [show hooks.peerRelease = (fun peer => liftWGPrefix (peerPut peer)) from rfl,
    HandshakeSecurity.StagedDisposal.Lifecycle.removeAll_neutral]
  unfold removeAllWith peerRemoveAllWith
  repeat' first
    | (coverage_head afterDeadWith; exact remove_after _)
    | (coverage_head Driver.Hooks.peerRelease; exact state_lift _)
    | coverage_state_step

theorem config_out (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StateAt frames (Driver.configOut hooks attrs peer ret) := by
  unfold Driver.configOut
  repeat' first
    | (coverage_head Driver.Hooks.peerRelease; exact state_lift _)
    | coverage_state_step

theorem config_finish (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    StateAt frames (Driver.configTailFinish hooks attrs peer pid ret) :=
  peer_finish _ (fun a p r _ => config_out a p r) attrs peer pid ret

theorem config_tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    StateAt frames (Driver.configTail hooks attrs peer pid) := by
  unfold Driver.configTail peerAllowedIpsWith
  repeat' first
    | (coverage_head Driver.configOut; exact config_out _ _ _)
    | (coverage_head Driver.configTailFinish; exact config_finish _ _ _ _)
    | (coverage_head Driver.Hooks.peerRelease; exact state_lift _)
    | coverage_state_step

theorem config_update (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StateAt frames (Driver.configUpdate hooks attrs peer flags psk pid) := by
  unfold Driver.configUpdate peerConfigUpdateWith
  repeat' first
    | (coverage_head Driver.configOut; exact config_out _ _ _)
    | (coverage_head Driver.configTail; exact config_tail _ _ _)
    | (coverage_head Driver.removeObserved; exact remove _)
    | (coverage_head Driver.Hooks.peerRelease; exact state_lift _)
    | coverage_state_step

theorem config_peer (attrs : PeerAttrs) : StateAt frames (Driver.configPeer hooks attrs) := by
  unfold Driver.configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (coverage_head Driver.configOut; exact config_out _ _ _)
    | (coverage_head Driver.configUpdate; exact config_update _ _ _ _ _)
    | (coverage_head Driver.Hooks.peerRelease; exact state_lift _)
    | coverage_state_step

theorem config_peers (attrs : DeviceAttrs) : StateAt frames (Driver.configPeers hooks attrs) := by
  unfold Driver.configPeers devicePeersWith
  repeat' first
    | (coverage_head Driver.configPeer; exact config_peer _)
    | (coverage_head Driver.Hooks.peerRelease; exact state_lift _)
    | coverage_state_step

theorem config_key (attrs : DeviceAttrs) : StateAt frames (Driver.configKey hooks attrs) := by
  unfold Driver.configKey deviceKeyWith
  repeat' first
    | (coverage_head FixtureEffects.runWith; apply fixture; intro frames live)
    | (coverage_head Driver.configPeers; exact config_peers _)
    | (coverage_head Driver.removeObserved; exact remove _)
    | (coverage_head Driver.stagingObserved; exact staging _ (by assumption))
    | (coverage_head Driver.Hooks.peerRelease; exact state_lift _)
    | coverage_state_step

theorem config_device_update (attrs : DeviceAttrs) (flags : UInt32) :
    StateAt frames (Driver.configDeviceUpdate hooks attrs flags) := by
  unfold Driver.configDeviceUpdate deviceUpdateWith
  repeat' first
    | (coverage_head Driver.configKey; exact config_key _)
    | (coverage_head Driver.removeAllObserved; exact remove_all)
    | (coverage_head Driver.Hooks.peerRelease; exact state_lift _)
    | coverage_state_step

theorem config_device (attrs : DeviceAttrs) : StateAt frames (Driver.configDevice hooks attrs) := by
  unfold Driver.configDevice setDeviceWith
  repeat' first
    | (coverage_head Driver.configDeviceUpdate; exact config_device_update _ _)
    | (coverage_head Driver.Hooks.peerRelease; exact state_lift _)
    | coverage_state_step

theorem up : StateAt frames (Driver.upObserved hooks) := by
  unfold Driver.upObserved
  repeat' first
    | (coverage_head Driver.openObserved; exact interface_open)
    | (coverage_head Driver.Hooks.peerRelease; exact state_lift _)
    | coverage_state_step

theorem down : StateAt frames (Driver.downObserved hooks) := by
  unfold Driver.downObserved
  rw [show hooks.stagedPurge = (fun pid => liftWGPrefix (purgeStagedPackets pid)) from rfl,
    HandshakeSecurity.StagedDisposal.Lifecycle.down_neutral]
  unfold downWith stopWith timersStopWith
  repeat' first
    | (coverage_head Driver.sendDrainObserved; exact send_drain _)
    | (coverage_head Driver.Hooks.peerRelease; exact state_lift _)
    | coverage_state_step

theorem destruct : StateAt frames (Driver.destructObserved hooks) := by
  change StateAt frames (Configuration.destructWith liftWGPrefix (Driver.removeAllObserved hooks) _)
  unfold Configuration.destructWith
  repeat' first
    | (coverage_head Driver.removeAllObserved; exact remove_all)
    | (coverage_head Driver.Hooks.peerRelease; exact state_lift _)
    | coverage_state_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
