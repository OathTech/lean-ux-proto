import Leanux.Proofs.WG.Progress.HandshakeFiniteSource
import Leanux.Proofs.WG.Noise.PeerInitializationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.PeerFinite
open Leanux Leanux.WG

/-- Static-static precomputation with the finite curve evaluator at its
original guarded call. The no-identity arm does not evaluate the curve. -/
def precompute (pid : PeerId) : WG.M Unit := do
  requireNotPending pid "recomputing the static-static key"
  let identity := (← getDev).staticIdentity
  let p ← getPeer pid
  let zero ← do
    if ← branch .precomputeNoIdentity !identity.hasIdentity then pure true
    else
      let (out, nonNull) ← HandshakeFinite.curve identity.staticPrivate p.remoteStatic
      setPeer pid { p with precomputedStaticStatic := out }
      branch .precomputeNullPoint !nonNull
  if zero then setPeer pid { (← getPeer pid) with precomputedStaticStatic := List.replicate 32 0 }

theorem precompute_source (pid : PeerId) :
    WG.precomputeStaticStatic pid = precompute pid := by
  simp only [precompute, HandshakeFinite.curve_source, pure_bind]
  rfl

/-- Finite identity installation. Public-key generation receives the original
input bytes; only the stored private key is clamped, as in the native source. -/
def setPrivate (privateKey : Key) : WG.M Unit := do
  for pid in (← getDev).peerList do requireNotPending pid "changing the device identity"
  let clamped := clamp privateKey
  let (pub, has) ← HandshakeFinite.generatePublic privateKey
  modifyDev fun d => { d with staticIdentity := { hasIdentity := has, staticPrivate := clamped, staticPublic := pub.getD d.staticIdentity.staticPublic } }

theorem setPrivate_source (privateKey : Key) :
    WG.setStaticIdentityPrivateKey privateKey = setPrivate privateKey := by
  unfold setPrivate
  rw [← HandshakeFinite.generatePublic_source]
  rfl

/-- The existing initialization factor with only its final precomputation
replaced. Entry-word and optional PSK writes remain in source order. -/
def handshakeInit (pid : PeerId) (psk : Option Key) : WG.M Unit := do
  Noise.modifyPeer pid (fun p => {p with handshakeEntryPeer := some pid})
  if ← branch .handshakeInitHasPsk psk.isSome then
    Noise.modifyPeer pid (fun p => {p with presharedKey := psk.getD p.presharedKey})
  precompute pid

theorem handshakeInit_source (pid : PeerId) (psk : Option Key) :
    WG.handshakeInit pid psk = handshakeInit pid psk := by
  rw [Noise.handshakeInit_source]
  unfold handshakeInit
  rw [← precompute_source]

end Leanux.Proofs.WG.Progress.PeerFinite
