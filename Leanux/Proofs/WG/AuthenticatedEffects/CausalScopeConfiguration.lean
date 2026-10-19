import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeFixture
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeSend

/-! Configuration and lifecycle callbacks restore scopes even when they drain
queued handshake work. Only the exact guarded fixture sites enter local roots. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes Queues Configuration
open HandshakeSecurity.SendExchange
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem send_drain (upTo : Option PeerId) : StateSafe (Driver.sendDrainObserved hooks upTo) := by
  unfold Driver.sendDrainObserved drainWith
  repeat' first
    | (scope_balance_head Driver.Hooks.flushedSend; exact flushed_send _)
    | scope_state_step

theorem remove_after (pid : PeerId) : StateSafe (afterDeadWith liftWGPrefix (Driver.sendDrainObserved hooks) pid) := by
  unfold afterDeadWith timersStopWith
  repeat' first
    | (scope_balance_head Driver.sendDrainObserved; exact send_drain _)
    | scope_state_step

theorem remove (peer : Option PeerId) : StateSafe (Driver.removeObserved hooks peer) := by
  unfold Driver.removeObserved removeWith peerRemoveWith
  repeat' first
    | (scope_balance_head afterDeadWith; exact remove_after _)
    | scope_state_step

theorem remove_all : StateSafe (Driver.removeAllObserved hooks) := by
  unfold Driver.removeAllObserved removeAllWith peerRemoveAllWith
  repeat' first
    | (scope_balance_head afterDeadWith; exact remove_after _)
    | scope_state_step

theorem config_out (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StateSafe (Driver.configOut attrs peer ret) := by
  unfold Driver.configOut
  repeat' scope_state_step

theorem config_finish (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    StateSafe (Driver.configTailFinish hooks attrs peer pid ret) :=
  peer_finish _ config_out attrs peer pid ret

theorem config_tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    StateSafe (Driver.configTail hooks attrs peer pid) := by
  unfold Driver.configTail peerAllowedIpsWith
  repeat' first
    | (scope_balance_head Driver.configOut; exact config_out _ _ _)
    | (scope_balance_head Driver.configTailFinish; exact config_finish _ _ _ _)
    | scope_state_step

theorem config_update (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StateSafe (Driver.configUpdate hooks attrs peer flags psk pid) := by
  unfold Driver.configUpdate peerConfigUpdateWith
  repeat' first
    | (scope_balance_head Driver.configOut; exact config_out _ _ _)
    | (scope_balance_head Driver.configTail; exact config_tail _ _ _)
    | (scope_balance_head Driver.removeObserved; exact remove _)
    | scope_state_step

theorem config_peer (attrs : PeerAttrs) : StateSafe (Driver.configPeer hooks attrs) := by
  unfold Driver.configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (scope_balance_head Driver.configOut; exact config_out _ _ _)
    | (scope_balance_head Driver.configUpdate; exact config_update _ _ _ _ _)
    | scope_state_step

theorem config_peers (attrs : DeviceAttrs) : StateSafe (Driver.configPeers hooks attrs) := by
  unfold Driver.configPeers devicePeersWith
  repeat' first
    | (scope_balance_head Driver.configPeer; exact config_peer _)
    | scope_state_step

theorem config_key (attrs : DeviceAttrs) : StateSafe (Driver.configKey hooks attrs) := by
  unfold Driver.configKey deviceKeyWith
  repeat' first
    | (scope_balance_head FixtureEffects.runWith; apply fixture)
    | (scope_balance_head Driver.configPeers; exact config_peers _)
    | (scope_balance_head Driver.removeObserved; exact remove _)
    | (scope_balance_head Driver.stagingObserved; exact staging _)
    | scope_state_step

theorem config_device_update (attrs : DeviceAttrs) (flags : UInt32) :
    StateSafe (Driver.configDeviceUpdate hooks attrs flags) := by
  unfold Driver.configDeviceUpdate deviceUpdateWith
  repeat' first
    | (scope_balance_head Driver.configKey; exact config_key _)
    | (scope_balance_head Driver.removeAllObserved; exact remove_all)
    | scope_state_step

theorem config_device (attrs : DeviceAttrs) : StateSafe (Driver.configDevice hooks attrs) := by
  unfold Driver.configDevice setDeviceWith
  repeat' first
    | (scope_balance_head Driver.configDeviceUpdate; exact config_device_update _ _)
    | scope_state_step

theorem up : StateSafe (Driver.upObserved hooks) := by
  unfold Driver.upObserved
  repeat' first
    | (scope_balance_head Driver.openObserved; exact interface_open)
    | scope_state_step

theorem down : StateSafe (Driver.downObserved hooks) := by
  unfold Driver.downObserved downWith stopWith timersStopWith
  repeat' first
    | (scope_balance_head Driver.sendDrainObserved; exact send_drain _)
    | scope_state_step

theorem destruct : StateSafe (Driver.destructObserved hooks) := by
  change StateSafe (Configuration.destructWith liftWGPrefix (Driver.removeAllObserved hooks) _)
  unfold Configuration.destructWith
  repeat' first
    | (scope_balance_head Driver.removeAllObserved; exact remove_all)
    | scope_state_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
