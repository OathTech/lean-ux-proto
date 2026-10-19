import Leanux.Proofs.WG.TransmitSecurity.StagedRemoval
import Leanux.Proofs.WG.TransmitSecurity.StagedSavedPeer

/-! Complete native configuration carries the same positional staged origins
through guarded sends, saved metadata writes and peer removal drains. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open Driver AuthenticatedEffects AuthenticatedEffects.CausalJournal HandshakeSecurity
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option pp.structureInstances false

theorem config_out (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StateSafe (configOut attrs peer ret) := by
  unfold configOut
  repeat' staged_configuration_step

private theorem finish_end (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId)
    (ret : Int) (running : Bool) : StateSafe (do
      if ← liftWGPrefix (branch .peerRunning running) then
        FixtureEffects.runWith (fixtureOps hooks) (.peerConfiguration attrs pid .staging)
          (stagingObserved hooks pid)
      configOut attrs peer ret) := by
  apply state_bind
  · apply state_lift; intro history; unfold branch; exact hoare_liftAmbient _ _
  intro active
  split
  · exact state_bind (fixture _ _ (staging_observed pid)) (fun _ => config_out attrs peer ret)
  · exact config_out attrs peer ret

theorem config_finish (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    StateSafe (configTailFinish hooks attrs peer pid ret) := by
  unfold configTailFinish FixtureEffects.peerFinishObserved FixtureEffects.peerFinishWith
  apply state_bind (state_lift _ (fun _ => Native.store getDev_sameWGStore))
  intro d
  apply state_bind
  · apply state_lift; intro history; unfold branch; exact hoare_liftAmbient _ _
  intro keep
  cases keep with
  | false => exact finish_end attrs peer pid ret d.running
  | true =>
    dsimp only
    apply StatePrefixEnsures.bind (SavedPeer.read pid)
    intro p
    apply StatePrefixEnsures.bind (SavedPeer.store pid p _ (Native.keepalive_decision p _ d.running))
    intro send
    apply StatePrefixEnsures.bind (SavedPeer.write pid p
      (fun p => {p with persistentKeepaliveInterval := attrs.keepalive.getD 0}) (fun _ => ⟨rfl,rfl⟩))
    intro _
    apply state_bind
    · apply state_lift; intro history; unfold branch; exact hoare_liftAmbient _ _
    intro now
    cases now with
    | false => exact finish_end attrs peer pid ret d.running
    | true =>
      exact state_bind (fixture _ _ (keepalive_observed_source pid))
        (fun _ => finish_end attrs peer pid ret d.running)

macro "staged_config_step" : tactic => `(tactic| first
  | (staged_effect_update_head; first
      | (apply state_read_modify; intro p; exact ⟨rfl,rfl⟩)
      | (apply state_read_write; · intro p; exact ⟨rfl,rfl⟩))
  | (staged_origin_head FixtureEffects.runWith; apply fixture)
  | (staged_origin_head configOut; exact config_out _ _ _)
  | (staged_origin_head configTailFinish; exact config_finish _ _ _ _)
  | (staged_origin_head removeObserved; exact remove_peer _)
  | (staged_origin_head removeAllObserved; exact remove_all)
  | (staged_origin_head stagingObserved; exact staging_observed _)
  | (staged_origin_head keepaliveObserved; exact keepalive_observed_source _)
  | (staged_origin_head liftWGPrefix
     apply state_lift; intro history
     simp only [WG.andM,WG.orM]
     repeat' staged_configuration_native
     done)
  | staged_configuration_step)

theorem config_tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    StateSafe (configTail hooks attrs peer pid) := by
  unfold configTail peerAllowedIpsWith
  repeat' staged_config_step

theorem config_update (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) : StateSafe (configUpdate hooks attrs peer flags psk pid) := by
  unfold configUpdate peerConfigUpdateWith
  repeat' first
    | (staged_origin_head configTail; exact config_tail _ _ _)
    | staged_config_step

theorem config_peer (attrs : PeerAttrs) : StateSafe (configPeer hooks attrs) := by
  unfold configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (staged_origin_head configUpdate; exact config_update _ _ _ _ _)
    | staged_config_step

theorem config_peers (attrs : DeviceAttrs) : StateSafe (configPeers hooks attrs) := by
  unfold configPeers devicePeersWith
  repeat' first
    | (staged_origin_head configPeer; exact config_peer _)
    | staged_config_step

theorem config_key (attrs : DeviceAttrs) : StateSafe (configKey hooks attrs) := by
  unfold configKey deviceKeyWith
  repeat' first
    | (staged_origin_head configPeers; exact config_peers _)
    | staged_config_step

theorem config_device_update (attrs : DeviceAttrs) (flags : UInt32) :
    StateSafe (configDeviceUpdate hooks attrs flags) := by
  unfold configDeviceUpdate deviceUpdateWith
  repeat' first
    | (staged_origin_head configKey; exact config_key _)
    | staged_config_step

theorem config_device (attrs : DeviceAttrs) : StateSafe (configDevice hooks attrs) := by
  unfold configDevice setDeviceWith
  repeat' first
    | (staged_origin_head configDeviceUpdate; exact config_device_update _ _)
    | staged_config_step

theorem opened : StateSafe (openObserved hooks) := by
  unfold openObserved FixtureEffects.openObserved FixtureEffects.openWith
  repeat' staged_config_step

theorem up : StateSafe (upObserved hooks) := by
  unfold upObserved
  repeat' first
    | (staged_origin_head openObserved; exact opened)
    | staged_config_step

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
