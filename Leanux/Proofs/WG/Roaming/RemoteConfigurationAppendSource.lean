import Leanux.Proofs.WG.Roaming.RemoteConfigurationDeviceSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteConfiguration
open Leanux Leanux.WG Noise Lifetimes Queues Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Configuration

variable {E F α : Type}

variable (encode : RxHistory.Event → E) (decode : E → Option RxHistory.Event)

variable (birth : PeerCreateReceipt → E) (endpoint : EndpointRun → E)

theorem endpointObserved_appends (emit : EndpointRun → E) (pid : PeerId) (e : Endpoint) :
    StateAppends (endpointObserved encode decode emit pid e) :=
  (StateAppends.focus _ _ _).receiptWGObserved _

theorem birthObserved_appends (emit : PeerCreateReceipt → E) (key : Key) (psk : Option Key) :
    StateAppends (birthObserved encode decode emit key psk) :=
  (StateAppends.focus _ _ _).receiptWGObserved _

theorem update_appends (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) :
    StateAppends (update encode decode endpoint attrs peer flags psk pid) := by
  unfold update peerConfigUpdateWith
  repeat' first
    | (joint_append_head access; exact StateAppends.focus _ _ _)
    | (joint_append_head endpointObserved; exact endpointObserved_appends _ _ _ _ _)
    | (joint_append_head ForIn.forIn; apply TxDisposition.stateAppends_forIn)
    | joint_append_step

theorem acquired_appends (attrs : PeerAttrs) (key : Key) (psk : Option Key)
    (flags : UInt32) (peer : Option PeerId) :
    StateAppends (acquired encode decode birth endpoint attrs key psk flags peer) := by
  unfold acquired peerCommandAcquiredWith
  repeat' first
    | (joint_append_head access; exact StateAppends.focus _ _ _)
    | (joint_append_head birthObserved; exact birthObserved_appends _ _ _ _ _)
    | (joint_append_head update; exact update_appends _ _ _ _ _ _ _ _)
    | (joint_append_head ForIn.forIn; apply TxDisposition.stateAppends_forIn)
    | joint_append_step

theorem command_appends (attrs : PeerAttrs) :
    StateAppends (command encode decode birth endpoint attrs) := by
  unfold command setPeerCmdWith
  repeat' first
    | (joint_append_head access; exact StateAppends.focus _ _ _)
    | (joint_append_head acquired; exact acquired_appends _ _ _ _ _ _ _ _ _)
    | (joint_append_head ForIn.forIn; apply TxDisposition.stateAppends_forIn)
    | joint_append_step

theorem devicePeers_appends (attrs : DeviceAttrs) :
    StateAppends (devicePeers encode decode birth endpoint attrs) := by
  unfold devicePeers devicePeersWith
  repeat' first
    | (joint_append_head command; exact command_appends _ _ _ _ _)
    | (joint_append_head ForIn.forIn; apply TxDisposition.stateAppends_forIn)
    | joint_append_step

theorem deviceKey_appends (attrs : DeviceAttrs) :
    StateAppends (deviceKey encode decode birth endpoint attrs) := by
  unfold deviceKey deviceKeyWith
  repeat' first
    | (joint_append_head access; exact StateAppends.focus _ _ _)
    | (joint_append_head devicePeers; exact devicePeers_appends _ _ _ _ _)
    | (joint_append_head ForIn.forIn; apply TxDisposition.stateAppends_forIn)
    | joint_append_step

theorem deviceUpdate_appends (attrs : DeviceAttrs) (flags : UInt32) :
    StateAppends (deviceUpdate encode decode birth endpoint attrs flags) := by
  unfold deviceUpdate deviceUpdateWith
  repeat' first
    | (joint_append_head access; exact StateAppends.focus _ _ _)
    | (joint_append_head deviceKey; exact deviceKey_appends _ _ _ _ _)
    | (joint_append_head ForIn.forIn; apply TxDisposition.stateAppends_forIn)
    | joint_append_step

theorem setDevice_appends (attrs : DeviceAttrs) :
    StateAppends (setDevice encode decode birth endpoint attrs) := by
  unfold setDevice setDeviceWith
  repeat' first
    | (joint_append_head deviceUpdate; exact deviceUpdate_appends _ _ _ _ _ _)
    | (joint_append_head ForIn.forIn; apply TxDisposition.stateAppends_forIn)
    | joint_append_step

end Leanux.Proofs.WG.Roaming.RemoteConfiguration
