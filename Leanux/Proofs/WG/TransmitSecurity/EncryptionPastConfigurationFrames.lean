import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastPeerConfiguration
import Leanux.Proofs.WG.Queues.TxLiveDeviceConfiguration

/-! Device-configuration masks preserve the packet/device allocation frontiers
and pending encryption aliases used by historical exclusion. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.DeviceConfiguration
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TxDisposition

theorem configuration_frame {action : WG.M α} (same : SameConfiguration action) :
    Preserves (Ready past active) action := by
  apply ready_frame ((pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveDeviceConfiguration.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.configuration_frame) same)
  exact same.of_factor (fun k : WGOwnedView =>
    (⟨k.netIfindexNext,k.dev.map fun d => ⟨d.ifindex,d.nextSkb,d.encryptQueue.items⟩⟩ : View))
    view (fun w => by simp only [view,configurationView,configurationDevice,wgOwnedView,wgStoreView,
      Option.map_map,Function.comp_def])

theorem clear_endpoint (pid : PeerId) : Preserves (Ready past active) (clearPeerEndpointSrc pid) :=
  ready_frame (LiveFrontier.clear_endpoint pid) (EncryptionPast.clear_endpoint pid)

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.DeviceConfiguration
