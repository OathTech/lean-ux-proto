import Leanux.Proofs.WG.Roaming.InitiationCryptoEffects
import Leanux.Proofs.WG.Config.Returns

/-! Preserve arbitrary predicates of all former Kernel owners while recording
the actual crypto results through the product lift. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

theorem initiationKdf_two_returns (ck input : List UInt8)
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) :
    Config.Product.Returns (liftWG (kdf true false ck input))
      (fun w => P w.wg w.fs w.tasks w.seccomp)
      (fun outs w => outs = [responseFirst ck input, responseSecond ck input] ∧
        P w.wg w.fs w.tasks w.seccomp) := by
  intro w pre
  refine ⟨_, _, rfl, ?_⟩
  exact ⟨by simp [initiationKdf_two], pre⟩

theorem initiationDh_returns (ck priv pub : List UInt8)
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) :
    Config.Product.Returns (liftWG (mixDh true ck priv pub))
      (fun w => P w.wg w.fs w.tasks w.seccomp)
      (fun out w => P w.wg w.fs w.tasks w.seccomp ∧ ∀ result, out = some result →
        (curve25519 priv pub).2 = true ∧
        result = (responseFirst ck (curve25519 priv pub).1,
          responseSecond ck (curve25519 priv pub).1)) := by
  intro w pre
  cases ok : (curve25519 priv pub).2 with
  | false =>
    simp [mixDh, ok]
    refine ⟨_, _, rfl, pre, ?_⟩
    simp
  | true =>
    simp [mixDh, ok, kdf, initiationKdf_two, kdfOut]
    refine ⟨_, _, rfl, pre, ?_⟩
    simp_all

theorem initiationPrecomputed_returns (ck precomputed : List UInt8)
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) :
    Config.Product.Returns (liftWG (mixPrecomputedDh ck precomputed))
      (fun w => P w.wg w.fs w.tasks w.seccomp)
      (fun out w => P w.wg w.fs w.tasks w.seccomp ∧ ∀ result, out = some result →
        precomputed ≠ List.replicate 32 0 ∧
        result = (responseFirst ck precomputed, responseSecond ck precomputed)) := by
  intro w pre
  have zero : (noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.zeroKey) =
      List.replicate 32 0 := rfl
  by_cases equal : precomputed = List.replicate 32 0
  · simp [mixPrecomputedDh, zero, equal]
    refine ⟨_, _, rfl, pre, ?_⟩
    simp
  · have different : (precomputed == (noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.zeroKey)) = false := by
      change (precomputed == List.replicate 32 0) = false
      exact beq_eq_false_iff_ne.mpr equal
    simp [mixPrecomputedDh, different, kdf, initiationKdf_two, kdfOut]
    refine ⟨_, _, rfl, pre, ?_⟩
    simp_all

end Leanux.Proofs.WG.Roaming
