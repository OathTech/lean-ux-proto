import Leanux.Proofs.WG.Config.EndpointSetModel
import Leanux.Proofs.WG.Campaign2.View

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarPrefix
open Leanux Leanux.WG Noise Std.Do

def keyedPeer (p : Peer) (psk : Option Key) : Peer :=
  match psk with | none => p | some k => {p with presharedKey := k}

def keyedDevice (d : Device) (pid : PeerId) (p : Peer) (psk : Option Key) : Device :=
  match psk with | none => d | some k => withPeer d pid {p with presharedKey := k}

def effectPeer (p : Peer) (psk : Option Key) (endpoint : Option EndpointAttr)
    (reset : Option UInt64) : Peer :=
  match endpoint with
  | none => keyedPeer p psk
  | some a => endpointAttributePeer (keyedPeer p psk) a reset

def effectDevice (d : Device) (pid : PeerId) (p : Peer) (psk : Option Key)
    (endpoint : Option EndpointAttr) (reset : Option UInt64) : Device :=
  match endpoint with
  | none => keyedDevice d pid p psk
  | some a => endpointAttributeStores (keyedDevice d pid p psk) pid (keyedPeer p psk) a reset

structure Inspection where
  outcome : Campaign2.Outcome Int
  completed : Option Campaign2.Snapshot

def CutEffect (attrs : PeerAttrs) (psk : Option Key) (pid : PeerId) (d : Device) (p : Peer)
    (initial completed : Campaign2.Snapshot) : Prop :=
  ∃ reset, completed.wg.device=some (effectDevice d pid p psk attrs.endpoint reset) ∧
    completed.wg.nlSock7=initial.wg.nlSock7 ∧
    completed.wg.fixtureNetDevices=initial.wg.fixtureNetDevices

def Facts (attrs : PeerAttrs) (psk : Option Key) (pid : PeerId) (d : Device) (p : Peer)
    (initial : Campaign2.Snapshot) (result : Inspection) : Prop :=
  (∀ completed, result.completed=some completed → CutEffect attrs psk pid d p initial completed) ∧
  (result.completed=none → ∃stop,result.outcome=.error stop)

end Leanux.Proofs.WG.Config.ScalarPrefix
