import Leanux.Proofs.WG.Config.AllowedInsertModel
import Leanux.Proofs.WG.Config.PeerScalars

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Std.Do Lean

def mixedPeerAttrs (v4 : Bool) (key psk : Key) (interval addr cidr : Nat)
    (bad : Bool) : PeerAttrs :=
  { publicKey := some key, presharedKey := some psk, keepalive := some interval,
    allowedIps := some ([.attrs (allowedAttrs v4 addr cidr)] ++
      if bad then [.malformed] else []) }

def mixedPeerKeyed (p : Peer) (psk : Key) : Peer :=
  {p with refcount := p.refcount + 1, presharedKey := psk}

def mixedPeerBase (d : Device) (pid : PeerId) (p : Peer) (psk : Key) : Device :=
  withPeer (withPeer d pid {p with refcount := p.refcount + 1}) pid (mixedPeerKeyed p psk)

def mixedPeerExit (d : Device) (pid : PeerId) (p : Peer) (interval : Nat)
    (finish : Bool) : Device :=
  if finish then
    let configured := {p with persistentKeepaliveInterval := interval}
    withPeer (withPeer d pid configured) pid {configured with refcount := p.refcount - 1}
  else withPeer d pid {p with refcount := p.refcount - 1}

def MixedPeerEffect (v4 : Bool) (d : Device) (pid : PeerId) (p : Peer) (psk : Key)
    (interval addr cidr : Nat) (bad : Bool) (ret : Int) (final : Device) : Prop :=
  let keyed := mixedPeerKeyed p psk
  let base := mixedPeerBase d pid p psk
  (ret = -ENOMEM ∧ final = mixedPeerExit (insertSequenceDevice base) pid keyed interval false) ∨
  (ret = (if bad then -EINVAL else 0) ∧ final = mixedPeerExit
    (emptyRootInserted v4 (insertSequenceDevice base) pid keyed addr cidr) pid
    {keyed with allowedipsList := p.allowedipsList ++ [d.nextNode]} interval (!bad))

def mixedPeerReadback (p : Peer) (psk : Key) (interval id : Nat)
    (bad inserted : Bool) : Peer :=
  { p with
    presharedKey := psk
    allowedipsList := if inserted then p.allowedipsList ++ [id] else p.allowedipsList
    persistentKeepaliveInterval := if inserted && !bad then interval else p.persistentKeepaliveInterval}

end Leanux.Proofs.WG.Config
