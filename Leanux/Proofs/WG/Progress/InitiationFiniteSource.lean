import Leanux.Proofs.WG.Progress.HandshakeFiniteSource
import Leanux.Proofs.WG.Noise.InitiationReadySource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG
open Leanux.Proofs.WG.Noise.InitiationReady

/-- The complete initiation creator using the existing ordered source stages,
finite curve leaves, and the original bounded index insertion. No input-shape,
residency, non-null, record availability or successful-return premise is needed. -/
def createInitiation (pid : PeerId) : WG.M (Option (List UInt8)) := do
  let identity := (← getDev).staticIdentity
  if ← branch .initNoIdentity !identity.hasIdentity then return none
  let p ← getPeer pid
  bodyWith generatePublic mixDh pid identity.staticPublic p

theorem createInitiation_source (pid : PeerId) :
    WG.createInitiation pid = createInitiation pid := by
  rw [createInitiation_factored]
  unfold createInitiation body
  have publicSame : WG.generatePublic = generatePublic := funext generatePublic_source
  have dhSame : WG.mixDh = mixDh :=
    funext fun key => funext fun ck => funext fun priv => funext fun pub =>
      mixDh_source key ck priv pub
  rw [publicSame, dhSame]

end Leanux.Proofs.WG.Progress.HandshakeFinite
