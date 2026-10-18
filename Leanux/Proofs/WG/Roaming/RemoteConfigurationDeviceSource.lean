import Leanux.Proofs.WG.Roaming.RemoteConfigurationPeerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteConfiguration
open Leanux Leanux.WG Noise Lifetimes Queues Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Configuration

variable {E F α : Type}

variable (encode : RxHistory.Event → E) (decode : E → Option RxHistory.Event)

variable (birth : PeerCreateReceipt → E) (endpoint : EndpointRun → E)

variable (law : ∀ e, decode (encode e) = some e)
  (birthIgnored : ∀ r, decode (birth r) = none)
  (endpointIgnored : ∀ r, decode (endpoint r) = none)
def devicePeers (attrs : DeviceAttrs) : WGPrefix E Int :=
  devicePeersWith (fun {_} a => liftWGPrefix a) (command encode decode birth endpoint) attrs

def deviceKey (attrs : DeviceAttrs) : WGPrefix E Int :=
  deviceKeyWith (fun {_} a => liftWGPrefix a)
    (fun k => access encode decode (pubkeyLookupPrefix k))
    (fun p => access encode decode (peerPutMixed p))
    (fun p => access encode decode (peerRemovePrefix p))
    (fun p => access encode decode (precomputeStaticStaticMixed p))
    (fun p => access encode decode (expireCurrentPeerKeypairsPrefix p))
    (fun p => access encode decode (sendStagedPacketsPrefix p))
    (devicePeers encode decode birth endpoint attrs) attrs

def deviceUpdate (attrs : DeviceAttrs) (flags : UInt32) : WGPrefix E Int :=
  deviceUpdateWith (fun {_} a => liftWGPrefix a)
    (fun p => access encode decode (clearPeerEndpointSrcPrefix p))
    (fun p => access encode decode (setPortPrefix p))
    (access encode decode peerRemoveAllPrefix)
    (deviceKey encode decode birth endpoint attrs) attrs flags

def setDevice (attrs : DeviceAttrs) : WGPrefix E Int :=
  setDeviceWith (fun {_} a => liftWGPrefix a) (deviceUpdate encode decode birth endpoint attrs) attrs

include law birthIgnored endpointIgnored in
theorem devicePeers_projects (attrs : DeviceAttrs) :
    StateProjectsPrefix decode id (devicePeers encode decode birth endpoint attrs)
      (RoutingJoint.nativeRx (devicePeersPrefix attrs)) := by
  rw [← (pinned_const _private.Leanux.Proofs.WG.Queues.JointDevice.«0».Leanux.Proofs.WG.Queues.RoutingJoint.devicePeers_rx_eq) attrs]
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointDevice.«0».Leanux.Proofs.WG.Queues.RoutingJoint.peers_projects) decode
  · exact fun {_} a =>
      (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) decode a
  · exact command_projects encode decode birth endpoint law birthIgnored endpointIgnored

include law birthIgnored endpointIgnored in
theorem deviceKey_projects (attrs : DeviceAttrs) :
    StateProjectsPrefix decode id (deviceKey encode decode birth endpoint attrs)
      (RoutingJoint.nativeRx (deviceKeyPrefix attrs)) := by
  rw [← (pinned_const _private.Leanux.Proofs.WG.Queues.JointDevice.«0».Leanux.Proofs.WG.Queues.RoutingJoint.deviceKey_rx_eq) attrs]
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointDevice.«0».Leanux.Proofs.WG.Queues.RoutingJoint.key_projects) decode
  · exact fun {_} a =>
      (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) decode a
  · exact fun _ => access_projects encode decode law _
  · exact fun _ => access_projects encode decode law _
  · exact fun _ => access_projects encode decode law _
  · exact fun _ => access_projects encode decode law _
  · exact fun _ => access_projects encode decode law _
  · exact fun _ => access_projects encode decode law _
  · exact devicePeers_projects encode decode birth endpoint law birthIgnored endpointIgnored attrs

include law birthIgnored endpointIgnored in
theorem deviceUpdate_projects (attrs : DeviceAttrs) (flags : UInt32) :
    StateProjectsPrefix decode id (deviceUpdate encode decode birth endpoint attrs flags)
      (RoutingJoint.nativeRx (deviceUpdatePrefix attrs flags)) := by
  rw [← (pinned_const _private.Leanux.Proofs.WG.Queues.JointDevice.«0».Leanux.Proofs.WG.Queues.RoutingJoint.deviceUpdate_rx_eq) attrs flags]
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointDevice.«0».Leanux.Proofs.WG.Queues.RoutingJoint.update_projects) decode
  · exact fun {_} a =>
      (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) decode a
  · exact fun _ => access_projects encode decode law _
  · exact fun _ => access_projects encode decode law _
  · exact access_projects encode decode law _
  · exact deviceKey_projects encode decode birth endpoint law birthIgnored endpointIgnored attrs

include law birthIgnored endpointIgnored in
theorem setDevice_projects (attrs : DeviceAttrs) :
    StateProjectsPrefix decode id (setDevice encode decode birth endpoint attrs)
      (RoutingJoint.nativeRx (wgSetDevicePrefix attrs)) := by
  rw [← (pinned_const _private.Leanux.Proofs.WG.Queues.JointDevice.«0».Leanux.Proofs.WG.Queues.RoutingJoint.setDevice_rx_eq) attrs]
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointDevice.«0».Leanux.Proofs.WG.Queues.RoutingJoint.device_projects) decode
  · exact fun {_} a =>
      (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) decode a
  · exact deviceUpdate_projects encode decode birth endpoint law birthIgnored endpointIgnored attrs

include law birthIgnored endpointIgnored in
theorem setDevice_erases (attrs : DeviceAttrs) :
    ErasesStatePrefix (setDevice encode decode birth endpoint attrs) (wgSetDevice attrs) := by
  intro w ambient h
  have projection := congrArg Prod.fst
    (setDevice_projects encode decode birth endpoint law birthIgnored endpointIgnored attrs w ambient h)
  have erased := (focusStatePrefix_erases RxHistory.Event.audit RxHistory.auditEvent
    (focusStatePrefix_erases AuditEvent.lifetime AuditEvent.lifetime?
      (wgSetDevicePrefix_erases attrs))) w ambient (h.filterMap decode)
  have same := projection.symm.trans erased
  change ((runWGPrefix (setDevice encode decode birth endpoint attrs) w ambient h).1.map
    (fun ((x,v),a) => ((x,v),a))) = _ at same
  change (runWGPrefix (setDevice encode decode birth endpoint attrs) w ambient h).1 = _
  cases run : (runWGPrefix (setDevice encode decode birth endpoint attrs) w ambient h).1 <;>
    simpa only [run,Except.map] using same

end Leanux.Proofs.WG.Roaming.RemoteConfiguration
