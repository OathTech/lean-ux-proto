import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryConfigurationTail
import Leanux.Proofs.WG.TransmitSecurity.JournalProjection

/-! Exact native counterparts of the enriched configuration observer.
These equations transport native allocation facts only; packet history and
receipt accounting are established by their separate source contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConfigurationErasure
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal

theorem out (attrs : PeerAttrs) (peer : Option PeerId) (ret : Int) :
    ErasesStatePrefix (Driver.configOut hooks attrs peer ret)
      (do peerPut peer; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret) := by
  apply NestedPeerRelease.projects_erases old? (Driver.configOut_projects hooks_projects attrs peer ret)
  apply NestedPeerRelease.projects_erases Journal.nonce?
    (Driver.configOut_projects Journal.hooks_projects attrs peer ret)
  rw [Driver.nonce_configOut_eq]
  exact Nonce.configOut_erases attrs peer ret

theorem tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    ErasesStatePrefix (Driver.configTail hooks attrs peer pid) (peerConfigTailSource attrs peer pid) := by
  apply NestedPeerRelease.projects_erases old? (Driver.configTail_projects hooks_projects attrs peer pid)
  apply NestedPeerRelease.projects_erases Journal.nonce?
    (Driver.configTail_projects Journal.hooks_projects attrs peer pid)
  rw [Driver.nonce_configTail_eq]
  exact Nonce.configTail_erases attrs peer pid

theorem update (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    ErasesStatePrefix (Driver.configUpdate hooks attrs peer flags psk pid)
      (peerConfigUpdateSource attrs peer flags psk pid) := by
  apply NestedPeerRelease.projects_erases old? (Driver.configUpdate_projects hooks_projects attrs peer flags psk pid)
  apply NestedPeerRelease.projects_erases Journal.nonce?
    (Driver.configUpdate_projects Journal.hooks_projects attrs peer flags psk pid)
  rw [Driver.nonce_configUpdate_eq]
  exact Nonce.configUpdate_erases attrs peer flags psk pid

theorem peer (attrs : PeerAttrs) :
    ErasesStatePrefix (Driver.configPeer hooks attrs) (setPeerCmd attrs) := by
  apply NestedPeerRelease.projects_erases old? (Driver.configPeer_projects hooks_projects attrs)
  apply NestedPeerRelease.projects_erases Journal.nonce? (Driver.configPeer_projects Journal.hooks_projects attrs)
  rw [Driver.nonce_configPeer_eq]
  exact Nonce.configPeer_erases attrs

theorem peers (attrs : DeviceAttrs) :
    ErasesStatePrefix (Driver.configPeers hooks attrs) (devicePeersSource attrs) := by
  apply NestedPeerRelease.projects_erases old? (Driver.configPeers_projects hooks_projects attrs)
  apply NestedPeerRelease.projects_erases Journal.nonce? (Driver.configPeers_projects Journal.hooks_projects attrs)
  rw [Driver.nonce_configPeers_eq]
  exact Nonce.configPeers_erases attrs

theorem key (attrs : DeviceAttrs) :
    ErasesStatePrefix (Driver.configKey hooks attrs) (deviceKeySource attrs) := by
  apply NestedPeerRelease.projects_erases old? (Driver.configKey_projects hooks_projects attrs)
  apply NestedPeerRelease.projects_erases Journal.nonce? (Driver.configKey_projects Journal.hooks_projects attrs)
  rw [Driver.nonce_configKey_eq]
  exact Nonce.configKey_erases attrs

theorem device_update (attrs : DeviceAttrs) (flags : UInt32) :
    ErasesStatePrefix (Driver.configDeviceUpdate hooks attrs flags) (deviceUpdateSource attrs flags) := by
  apply NestedPeerRelease.projects_erases old? (Driver.configDeviceUpdate_projects hooks_projects attrs flags)
  apply NestedPeerRelease.projects_erases Journal.nonce? (Driver.configDeviceUpdate_projects Journal.hooks_projects attrs flags)
  rw [Driver.nonce_configDeviceUpdate_eq]
  exact Nonce.configDeviceUpdate_erases attrs flags

theorem device (attrs : DeviceAttrs) :
    ErasesStatePrefix (Driver.configDevice hooks attrs) (wgSetDevice attrs) := by
  apply NestedPeerRelease.projects_erases old? (Driver.configDevice_projects hooks_projects attrs)
  apply NestedPeerRelease.projects_erases Journal.nonce? (Driver.configDevice_projects Journal.hooks_projects attrs)
  rw [Driver.nonce_configDevice_eq]
  exact Nonce.configDevice_erases attrs

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ConfigurationErasure
