import Leanux.Proofs.WG.Noise.ResponseTagFrames
import Leanux.Proofs.WG.Noise.RotationEffects
import Leanux.Proofs.WG.Config.ExpiryEffects

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

/-- Every actual ordered rotation write or keypair release preserves all peer
tags. Aliased slots and allocation identities remain in the relation. -/
theorem rotationRun_tagMap {pid : PeerId} {d final : Device} {actions : List RotationAction}
    (steps : RotationRun pid d actions final) :
    responseTagMap (some final) = responseTagMap (some d) := by
  induction steps with
  | nil => rfl
  | write d final change p rest resident tail ih =>
    refine ih.trans ?_
    exact tagMap_write d pid p (change.apply p) resident (by cases change <;> rfl)
  | put d middle final key rest release tail ih =>
    refine ih.trans ?_
    funext target
    simp only [responseTagMap,Option.bind_some,clearPut_peers release]

/-- Validity-only key writes retain all optional peer tags, including the
pure missing-key case (which is not an assertion of native normal return). -/
theorem invalidateDevice_tagMap (d : Device) (key : Option KeypairId) :
    responseTagMap (some (Config.invalidateDevice d key)) = responseTagMap (some d) := by
  cases key with
  | none => rfl
  | some id =>
    cases resident : d.keypairs[id]? <;>
      simp only [Config.invalidateDevice,resident] <;> rfl

end Leanux.Proofs.WG.Noise
