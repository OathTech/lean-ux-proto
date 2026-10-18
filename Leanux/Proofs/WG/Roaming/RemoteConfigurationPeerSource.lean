import Leanux.Proofs.WG.Roaming.RemoteConfigurationCaptureSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteConfiguration
open Leanux Leanux.WG Noise Lifetimes Queues Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Configuration

variable {E F α : Type}

variable (encode : RxHistory.Event → E) (decode : E → Option RxHistory.Event)

variable (birth : PeerCreateReceipt → E) (endpoint : EndpointRun → E)

def update (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) : WGPrefix E Int :=
  peerConfigUpdateWith (fun {_} a => liftWGPrefix a)
    (access encode decode (peerRemovePrefix peer))
    (access encode decode (modifyPeerKeysPrefix pid (fun p => {p with presharedKey := psk.getD []})))
    (access encode decode (removeByPeerPrefix pid))
    (endpointObserved encode decode endpoint pid)
    (fun ret => access encode decode (peerConfigOutPrefix attrs peer ret))
    (access encode decode (peerConfigTailPrefix attrs peer pid)) attrs flags psk

def acquired (attrs : PeerAttrs) (key : Key) (psk : Option Key)
    (flags : UInt32) (peer : Option PeerId) : WGPrefix E Int :=
  peerCommandAcquiredWith (fun {_} a => liftWGPrefix a)
    (birthObserved encode decode birth)
    (fun pid => access encode decode (peerGetMixed pid))
    (fun ret => access encode decode (peerConfigOutPrefix attrs none ret))
    (update encode decode endpoint attrs) key psk flags peer

def command (attrs : PeerAttrs) : WGPrefix E Int :=
  setPeerCmdWith (fun {_} a => liftWGPrefix a)
    (fun key => access encode decode (pubkeyLookupPrefix key))
    (fun ret => access encode decode (peerConfigOutPrefix attrs none ret))
    (acquired encode decode birth endpoint attrs) attrs

variable (law : ∀ e, decode (encode e) = some e)
  (birthIgnored : ∀ r, decode (birth r) = none)
  (endpointIgnored : ∀ r, decode (endpoint r) = none)

include law endpointIgnored in
theorem update_projects (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) :
    StateProjectsPrefix decode id (update encode decode endpoint attrs peer flags psk pid)
      (RoutingJoint.nativeRx (peerConfigUpdatePrefix attrs peer flags psk pid)) := by
  rw [← RoutingJoint.peerConfigUpdateRx_eq attrs peer flags psk pid (RoutingJoint.peerRemovePrefix_appends peer)]
  apply RoutingJoint.peerConfigUpdateWith_projects decode
  · exact fun {_} a =>
      (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) decode a
  · exact access_projects encode decode law _
  · exact access_projects encode decode law _
  · exact access_projects encode decode law _
  · exact endpointObserved_projects encode decode law endpoint endpointIgnored pid
  · exact fun _ => access_projects encode decode law _
  · exact access_projects encode decode law _

include law birthIgnored endpointIgnored in
theorem command_projects (attrs : PeerAttrs) :
    StateProjectsPrefix decode id (command encode decode birth endpoint attrs)
      (RoutingJoint.nativeRx (setPeerCmdPrefix attrs)) := by
  rw [← (pinned_const _private.Leanux.Proofs.WG.Queues.JointPeerCommand.«0».Leanux.Proofs.WG.Queues.RoutingJoint.command_rx_eq) attrs]
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointPeerCommand.«0».Leanux.Proofs.WG.Queues.RoutingJoint.command_projects) decode
  · exact fun {_} a =>
      (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) decode a
  · exact fun _ => access_projects encode decode law _
  · exact fun _ => access_projects encode decode law _
  · intro key psk flags peer
    apply (pinned_const _private.Leanux.Proofs.WG.Queues.JointPeerCommand.«0».Leanux.Proofs.WG.Queues.RoutingJoint.acquired_projects) decode
    · exact fun {_} a =>
        (pinned_const _private.Leanux.Proofs.WG.Queues.JointConfiguration.«0».Leanux.Proofs.WG.Queues.RoutingJoint.project_lift) decode a
    · exact birthObserved_projects encode decode law birth birthIgnored
    · exact fun _ => access_projects encode decode law _
    · exact fun _ => access_projects encode decode law _
    · exact update_projects encode decode endpoint law endpointIgnored attrs

end Leanux.Proofs.WG.Roaming.RemoteConfiguration
