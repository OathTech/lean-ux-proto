import Leanux.Proofs.WG.TransmitSecurity.PacketOriginDriverTraffic
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginConfigurationFrames

/-! Peer/device configuration and opening a device transport allocation
origins through the same observed staging and keepalive callbacks. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Configuration Driver NativeFrames
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem state_forIn {α β : Type} (xs : List α) (init : β) (f : α → β → WGPrefix Journal.Event (ForInStep β))
    (hf : ∀ x b, StatePrefixPreserves (fun h w _ => JournalInv h w) Safe (f x b)) : StateSafe (forIn xs init f) :=
  StatePrefixEnsures.forInInvariant xs init f (fun _ h w _ => JournalInv h w) Safe
    (fun _ _ _ _ hi => hi.2) hf

private theorem config_bind {g : WGPrefix Journal.Event α} {f : α → WGPrefix Journal.Event β}
    (hg : StatePrefixPreserves (fun h w _ => JournalInv h w) Safe g)
    (hf : ∀ x, StatePrefixPreserves (fun h w _ => JournalInv h w) Safe (f x)) :
    StatePrefixPreserves (fun h w _ => JournalInv h w) Safe (g >>= f) := StatePrefixEnsures.bind hg hf

macro "origin_config_step" : tactic => `(tactic| first
  | origin_carrier_join_let
  | origin_carrier_join_use
  | (origin_native_lift; solve | apply state_lift; intro h; repeat' origin_configuration_frame)
  | (nonce_source_head Pure.pure; exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.2) (fun _ _ _ hi => hi))
  | (nonce_source_head ForIn.forIn; apply state_forIn)
  | (nonce_source_head Bind.bind; apply config_bind)
  | maintenance_intro
  | origin_carrier_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

theorem configOut_safe (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    StateSafe (configOut attrs peer ret) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold configOut
  repeat' origin_config_step

theorem configTailFinish_safe (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    StateSafe (configTailFinish Journal.hooks attrs peer pid ret) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold configTailFinish
  repeat' first
    | (nonce_source_head configOut; exact configOut_safe _ _ _)
    | (nonce_source_head stagingObserved; exact staging _)
    | (nonce_source_head keepaliveObserved; exact keepalive _)
    | origin_config_step

theorem configTail_safe (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) :
    StateSafe (configTail Journal.hooks attrs peer pid) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold configTail peerAllowedIpsWith
  repeat' first
    | (nonce_source_head configOut; exact configOut_safe _ _ _)
    | (nonce_source_head configTailFinish; exact configTailFinish_safe _ _ _ _)
    | origin_config_step

theorem configUpdate_safe (attrs : PeerAttrs)
    (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StateSafe (configUpdate Journal.hooks attrs peer flags psk pid) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold configUpdate peerConfigUpdateWith
  simp only [remove_lift Journal.hooks rfl]
  repeat' first
    | (nonce_source_head configOut; exact configOut_safe _ _ _)
    | (nonce_source_head configTail; exact configTail_safe _ _ _)
    | origin_config_step

theorem configPeer_safe (attrs : PeerAttrs) :
    StateSafe (configPeer Journal.hooks attrs) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold configPeer setPeerCmdWith peerCommandAcquiredWith
  repeat' first
    | (nonce_source_head configOut; exact configOut_safe _ _ _)
    | (nonce_source_head configUpdate; exact configUpdate_safe _ _ _ _ _)
    | origin_config_step

theorem configPeers_safe (attrs : DeviceAttrs) :
    StateSafe (configPeers Journal.hooks attrs) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold configPeers devicePeersWith
  repeat' first
    | (nonce_source_head configPeer; exact configPeer_safe _)
    | origin_config_step

theorem configKey_safe (attrs : DeviceAttrs) :
    StateSafe (configKey Journal.hooks attrs) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold configKey deviceKeyWith
  simp only [remove_lift Journal.hooks rfl]
  repeat' first
    | (nonce_source_head configPeers; exact configPeers_safe _)
    | (nonce_source_head stagingObserved; exact staging _)
    | origin_config_step

theorem configDeviceUpdate_safe (attrs : DeviceAttrs) (flags : UInt32) :
    StateSafe (configDeviceUpdate Journal.hooks attrs flags) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold configDeviceUpdate deviceUpdateWith
  simp only [removeAll_lift Journal.hooks rfl]
  repeat' first
    | (nonce_source_head configKey; exact configKey_safe _)
    | origin_config_step

theorem configDevice_safe (attrs : DeviceAttrs) :
    StateSafe (configDevice Journal.hooks attrs) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold configDevice setDeviceWith
  repeat' first
    | (nonce_source_head configDeviceUpdate; exact configDeviceUpdate_safe _ _)
    | origin_config_step

theorem opened :
    StateSafe (openObserved Journal.hooks) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold openObserved
  repeat' first
    | (nonce_source_head stagingObserved; exact staging _)
    | (nonce_source_head keepaliveObserved; exact keepalive _)
    | origin_config_step

theorem up :
    StateSafe (upObserved Journal.hooks) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  unfold upObserved
  repeat' first
    | (nonce_source_head openObserved; exact opened)
    | origin_config_step


end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
