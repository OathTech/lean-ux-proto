import Leanux.Proofs.WG.Progress.CurveEvaluationSource

/-! Concrete original curve outputs for the initialized give-up recipe.
These kernel-checked equalities supply no whole-operation or runner acceptance claim.
Raw inputs and the actual callers' clamped inputs are both retained. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.TimerDiscipline.InitializedGiveUp
open Leanux.WG Leanux.Proofs.WG.Progress

/-- The private key in the initialized give-up recipe. -/
def configuredSecret : Key := List.replicate 32 0x11

/-- Exact original curve result for the configured key/basepoint. The finite
power computation succeeds; no fallback inversion value is supplied. -/
theorem configured_curve_output :
    curve25519 configuredSecret basePoint =
      ([123, 78, 144, 155, 190, 127, 254, 68, 196, 101, 162, 32, 3, 125, 96, 142,
        227, 88, 151, 211, 30, 249, 114, 240, 127, 116, 137, 44, 176, 247, 63, 19], true) := by
  have evaluated : powEval p25519 256
      (1, (x25519Ladder configuredSecret basePoint).2 % p25519, p25519 - 2) =
        some (36867947142945818018149491544700130077922219265839395806449548058773750697662,
          45891194718051756346668487166418346924491685813618193551600130077632454380664, 0) := by
    decide +kernel
  unfold curve25519
  rw [x25519_of_evaluation configuredSecret basePoint 256 _ evaluated]
  decide +kernel

end Leanux.Proofs.WG.TimerDiscipline.InitializedGiveUp

namespace Leanux.Proofs.WG.TimerDiscipline.InitializedGiveUp
open Leanux.WG Leanux.Proofs.WG.Progress
def configuredRemote : Key := [15, 170, 104, 78, 210, 136, 103, 185, 127, 74, 106, 45, 238, 93, 248, 206, 151, 78, 118, 183, 1, 142, 63, 34, 161, 196, 207, 38, 120, 87, 15, 32]
def configuredEphemeral : Key := [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]

/-- Exact raw-input and actual caller-clamped curve values in the give-up recipe.
No assertion of whole-operation acceptance or timer effects is made. -/
theorem configured_remote_curve_output :
    curve25519 configuredSecret configuredRemote = ([158, 0, 64, 152, 239, 192, 145, 212, 236, 38, 99, 180, 233, 245, 207, 212, 215, 6, 69, 113, 105, 11, 75, 234, 151, 171, 20, 106, 185, 243, 80, 86], true) ∧
    curve25519 (clamp configuredSecret) configuredRemote = ([158, 0, 64, 152, 239, 192, 145, 212, 236, 38, 99, 180, 233, 245, 207, 212, 215, 6, 69, 113, 105, 11, 75, 234, 151, 171, 20, 106, 185, 243, 80, 86], true) := by
  have evaluated : powEval p25519 256
      (1, (x25519Ladder configuredSecret configuredRemote).2 % p25519, p25519 - 2) =
        some (10353280586857657690265903349309145008628376085795522905760100546020490725948, 35389933179687464766631390779210502991093053763944507589128154305338106568980, 0) := by
    decide +kernel
  have raw : curve25519 configuredSecret configuredRemote = ([158, 0, 64, 152, 239, 192, 145, 212, 236, 38, 99, 180, 233, 245, 207, 212, 215, 6, 69, 113, 105, 11, 75, 234, 151, 171, 20, 106, 185, 243, 80, 86], true) := by
    unfold curve25519
    rw [x25519_of_evaluation configuredSecret configuredRemote 256 _ evaluated]
    decide +kernel
  refine ⟨raw, ?_⟩
  have clampedEvaluation : powEval p25519 256
      (1, (x25519Ladder (clamp configuredSecret) configuredRemote).2 % p25519, p25519 - 2) =
        some (10353280586857657690265903349309145008628376085795522905760100546020490725948, 35389933179687464766631390779210502991093053763944507589128154305338106568980, 0) := by
    decide +kernel
  unfold curve25519
  rw [x25519_of_evaluation (clamp configuredSecret) configuredRemote 256 _ clampedEvaluation]
  decide +kernel

/-- Exact raw-input and actual caller-clamped curve values in the give-up recipe.
No assertion of whole-operation acceptance or timer effects is made. -/
theorem ephemeral_base_curve_output :
    curve25519 configuredEphemeral basePoint = ([136, 49, 134, 184, 0, 180, 29, 92, 240, 66, 150, 149, 218, 155, 60, 196, 243, 40, 235, 205, 24, 74, 110, 72, 47, 165, 120, 193, 3, 240, 108, 119], true) ∧
    curve25519 (clamp configuredEphemeral) basePoint = ([136, 49, 134, 184, 0, 180, 29, 92, 240, 66, 150, 149, 218, 155, 60, 196, 243, 40, 235, 205, 24, 74, 110, 72, 47, 165, 120, 193, 3, 240, 108, 119], true) := by
  have evaluated : powEval p25519 256
      (1, (x25519Ladder configuredEphemeral basePoint).2 % p25519, p25519 - 2) =
        some (42530273680311745071181821607171435996865730090243428932886594789649932501517, 36590386370576356176104717953862854332861452472770273937757010500001608990836, 0) := by
    decide +kernel
  have raw : curve25519 configuredEphemeral basePoint = ([136, 49, 134, 184, 0, 180, 29, 92, 240, 66, 150, 149, 218, 155, 60, 196, 243, 40, 235, 205, 24, 74, 110, 72, 47, 165, 120, 193, 3, 240, 108, 119], true) := by
    unfold curve25519
    rw [x25519_of_evaluation configuredEphemeral basePoint 256 _ evaluated]
    decide +kernel
  refine ⟨raw, ?_⟩
  have clampedEvaluation : powEval p25519 256
      (1, (x25519Ladder (clamp configuredEphemeral) basePoint).2 % p25519, p25519 - 2) =
        some (42530273680311745071181821607171435996865730090243428932886594789649932501517, 36590386370576356176104717953862854332861452472770273937757010500001608990836, 0) := by
    decide +kernel
  unfold curve25519
  rw [x25519_of_evaluation (clamp configuredEphemeral) basePoint 256 _ clampedEvaluation]
  decide +kernel

/-- Exact raw-input and actual caller-clamped curve values in the give-up recipe.
No assertion of whole-operation acceptance or timer effects is made. -/
theorem ephemeral_remote_curve_output :
    curve25519 configuredEphemeral configuredRemote = ([39, 114, 250, 146, 193, 32, 79, 160, 57, 207, 160, 60, 149, 193, 182, 50, 62, 235, 173, 21, 254, 59, 238, 250, 13, 186, 111, 237, 90, 39, 85, 50], true) ∧
    curve25519 (clamp configuredEphemeral) configuredRemote = ([39, 114, 250, 146, 193, 32, 79, 160, 57, 207, 160, 60, 149, 193, 182, 50, 62, 235, 173, 21, 254, 59, 238, 250, 13, 186, 111, 237, 90, 39, 85, 50], true) := by
  have evaluated : powEval p25519 256
      (1, (x25519Ladder configuredEphemeral configuredRemote).2 % p25519, p25519 - 2) =
        some (12957251029842237073106229905813074355974081054837278274696892022482652750336, 27530429620371247598310968424828040852647985110043828724627699098062001737794, 0) := by
    decide +kernel
  have raw : curve25519 configuredEphemeral configuredRemote = ([39, 114, 250, 146, 193, 32, 79, 160, 57, 207, 160, 60, 149, 193, 182, 50, 62, 235, 173, 21, 254, 59, 238, 250, 13, 186, 111, 237, 90, 39, 85, 50], true) := by
    unfold curve25519
    rw [x25519_of_evaluation configuredEphemeral configuredRemote 256 _ evaluated]
    decide +kernel
  refine ⟨raw, ?_⟩
  have clampedEvaluation : powEval p25519 256
      (1, (x25519Ladder (clamp configuredEphemeral) configuredRemote).2 % p25519, p25519 - 2) =
        some (12957251029842237073106229905813074355974081054837278274696892022482652750336, 27530429620371247598310968424828040852647985110043828724627699098062001737794, 0) := by
    decide +kernel
  unfold curve25519
  rw [x25519_of_evaluation (clamp configuredEphemeral) configuredRemote 256 _ clampedEvaluation]
  decide +kernel
end Leanux.Proofs.WG.TimerDiscipline.InitializedGiveUp
