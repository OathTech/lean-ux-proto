import Leanux.Proofs.WG.Progress.CurveFiniteSource
import Leanux.WG.Handshake

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG

/-- Finite Curve25519 evaluation with explicit exhaustion; the source theorem
below rules out that failure for every pair of byte lists. -/
def curve (secret point : Key) : WG.M (Key × Bool) :=
  match curve25519Finite secret point with
  | some result => pure result
  | none => invariant "finite Curve25519 inversion exhausted"

theorem curve_source (secret point : Key) :
    curve secret point = pure (curve25519 secret point) := by
  simp only [curve, curve25519Finite_source]

def generatePublic (secret : Key) : WG.M (Option Key × Bool) := do
  if ← branch .genPublicNullSecret (secret == nullPoint) then return (none, false)
  let (pub, nonNull) ← curve secret basePoint
  return (some pub, nonNull)

theorem generatePublic_source (secret : Key) :
    WG.generatePublic secret = generatePublic secret := by
  simp only [generatePublic, curve_source, pure_bind]
  rfl

def mixDh (key : Bool) (chainingKey priv pub : Key) : WG.M (Option (Key × Key)) := do
  let (dh, nonNull) ← curve priv pub
  if ← branch .mixDhNull !nonNull then return none
  let outs ← kdf key false chainingKey dh
  return some (← kdfOut outs 0, ← if key then kdfOut outs 1 else pure [])

theorem mixDh_source (key : Bool) (chainingKey priv pub : Key) :
    WG.mixDh key chainingKey priv pub = mixDh key chainingKey priv pub := by
  simp only [mixDh, curve_source, pure_bind]
  rfl

end Leanux.Proofs.WG.Progress.HandshakeFinite
