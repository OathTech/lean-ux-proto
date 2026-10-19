import Leanux.Proofs.WG.Config.ScalarTailModel
import Leanux.Proofs.WG.Peers.CreationAccess

/-! Initial scalar image and projected normal command effect for a missing public-key target. Quiet exits and allocation refusal leave the WireGuard projection unchanged; successful creation uses the actual allocation stamp. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.CreationScalar
open Leanux Leanux.WG Noise Lifetimes
open PeerScalarRetention

def initCell (psk : Option Key) (c : Cell) : Cell :=
  (c.1,psk.getD c.2.1,c.2.2.1,c.2.2.2)

def newbornCell (stamp : Nat) : Cell := (stamp,List.replicate 32 0,0,none)

def initializedPeer (key : Key) (stamp : Nat) (psk : Option Key) : Peer :=
  {Peers.createdPeer key stamp with presharedKey:=psk.getD (List.replicate 32 0)}

def CommandEffect (attrs : PeerAttrs) (key : Key) (initial : Campaign2.State)
    (ret : Int) (final : Campaign2.Snapshot) : Prop :=
  (final.wg=initial ∧ (ret=0 ∨ ret=-ENOMEM)) ∨
  ∃pid,initial.device.map Device.nextPeer=some pid ∧ observation final pid=
    some (ScalarTail.tailCell attrs ret
      (ScalarTail.prefixCell (initializedPeer key (initial.peerCounter+1) attrs.presharedKey)
        attrs.presharedKey attrs.endpoint))

end Leanux.Proofs.WG.Config.CreationScalar
