import Leanux.WG.Handshake
import Leanux.Proofs.WG.Index.TableModel

set_option autoImplicit false

/-! Pure initiation output. Device updates retain the original ordered map writes;
we do not replace repeated inserts by an extensional-map assumption. -/
namespace Leanux.Proofs.WG.Noise.InitiationReady
open Leanux Leanux.WG

def first (ck data : List UInt8) : List UInt8 := hmacBlake2s (hmacBlake2s ck data) [1]
def second (ck data : List UInt8) : List UInt8 := hmacBlake2s (hmacBlake2s ck data) (first ck data ++ [2])
def chainDevice (pid : PeerId) (d : Device) (p : Peer) (ck hash : List UInt8) : Device :=
  {d with peers := d.peers.insert pid {p with chainingKey := ck, hash}}
def secretDevice (pid : PeerId) (d : Device) (p : Peer) (secret : List UInt8) : Device :=
  {d with peers := d.peers.insert pid {p with ephemeralPrivate := secret}}
/-- The exact message and Device after a successful original initiation. The
index is supplied by the first fresh draw after removing this handshake owner. -/
def result (pid : PeerId) (d : Device) (p : Peer) (ephemeral clock : List UInt8)
    (index : Nat) : List UInt8 × Device :=
  let h0 := noiseHash (handshakeInitHash ++ p.remoteStatic)
  let p1 := {p with chainingKey := handshakeInitChainingKey, hash := h0}
  let d1 := chainDevice pid d p handshakeInitChainingKey h0
  let secret := clamp ephemeral
  let p2 := {p1 with ephemeralPrivate := secret}
  let d2 := secretDevice pid d1 p1 secret
  let e := (curve25519 secret basePoint).1
  let ck1 := first handshakeInitChainingKey e
  let h1 := noiseHash (h0 ++ e)
  let p3 := {p2 with chainingKey := ck1, hash := h1}
  let d3 := chainDevice pid d2 p2 ck1 h1
  let dh := (curve25519 secret p.remoteStatic).1
  let ck2 := first ck1 dh
  let encStatic := aeadEncrypt (second ck1 dh) noiseNonce d.staticIdentity.staticPublic h1
  let h2 := noiseHash (h1 ++ encStatic)
  let p4 := {p3 with chainingKey := ck2, hash := h2}
  let d4 := chainDevice pid d3 p3 ck2 h2
  let ck3 := first ck2 p.precomputedStaticStatic
  let key3 := second ck2 p.precomputedStaticStatic
  let encTime := aeadEncrypt key3 noiseNonce (tai64n clock) h2
  let h3 := noiseHash (h2 ++ encTime)
  let p5 := {p4 with chainingKey := ck3, hash := h3}
  let d5 := chainDevice pid d4 p4 ck3 h3
  (le32 1 ++ le32 index ++ e ++ encStatic ++ encTime ++ List.replicate 32 0,
    {d5 with
      peers := d5.peers.insert pid {p5 with handshakeState := HANDSHAKE_CREATED_INITIATION}
      indexTable := {index, owner := .handshake pid} :: Index.removeOwner (.handshake pid) d.indexTable})


end Leanux.Proofs.WG.Noise.InitiationReady
