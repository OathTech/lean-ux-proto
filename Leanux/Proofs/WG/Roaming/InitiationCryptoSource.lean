import Leanux.Proofs.WG.Roaming.InitiationModel
import Leanux.Proofs.WG.Roaming.ResponseCryptoSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem initiationKdf_two (ck input : List UInt8) :
    kdfOutputs ck input 2 = [responseFirst ck input, responseSecond ck input] := by
  simp [kdfOutputs, responseFirst, responseSecond, List.range']

theorem initiationKdf_two_returns (ck input : List UInt8) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ kdf true false ck input
      ⦃⇓ outs w => ⌜outs = [responseFirst ck input, responseSecond ck input] ∧ P w.k⌝⦄ := by
  mvcgen [kdf, WG.orM, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [initiationKdf_two]

theorem initiationDh_returns (ck priv pub : List UInt8) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ mixDh true ck priv pub
      ⦃⇓ out w => ⌜P w.k ∧ ∀ result, out = some result →
        (curve25519 priv pub).2 = true ∧
        result = (responseFirst ck (curve25519 priv pub).1,
          responseSecond ck (curve25519 priv pub).1)⌝⦄ := by
  have hk := initiationKdf_two_returns ck (curve25519 priv pub).1 P
  mvcgen [mixDh, kdfOut, branch, invariant, hk]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals grind

theorem initiationPrecomputed_returns (ck precomputed : List UInt8) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ mixPrecomputedDh ck precomputed
      ⦃⇓ out w => ⌜P w.k ∧ ∀ result, out = some result →
        precomputed ≠ List.replicate 32 0 ∧
        result = (responseFirst ck precomputed, responseSecond ck precomputed)⌝⦄ := by
  have hz : (noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.zeroKey) = List.replicate 32 0 := rfl
  have hk := initiationKdf_two_returns ck precomputed P
  mvcgen [mixPrecomputedDh, kdfOut, branch, invariant, hk]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all only [hz]
  all_goals simp_all
  all_goals grind

end Leanux.Proofs.WG.Roaming
