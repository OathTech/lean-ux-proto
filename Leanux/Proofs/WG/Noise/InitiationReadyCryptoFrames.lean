import Leanux.Proofs.WG.Noise.InitiationReadyCryptoModel
import Leanux.Proofs.WG.Config.Returns

/-! Total crypto results and preservation through the actual product lift.
The predicate spans all subsystem owners of the former Kernel fields and
the ambient record stream; decision traces remain unrestricted. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise.InitiationReady
open Leanux Leanux.WG Leanux.Proofs.WG.Config

theorem kdf_returns (two : Bool) (ck data : List UInt8)
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Option (List HiddenRecord) → Prop) :
    Config.Product.Returns (liftWG (kdf two false ck data))
      (fun w => P w.wg w.fs w.tasks w.seccomp w.ambient.hidden)
      (fun out w => out = (if two then [first ck data, second ck data] else [first ck data]) ∧
        P w.wg w.fs w.tasks w.seccomp w.ambient.hidden) := by
  intro w pre
  cases two <;> refine ⟨_, _, rfl, ?_⟩
  all_goals exact ⟨by simp [kdf_pair, kdf_single], pre⟩

theorem ephemeral_returns (e ck hash : List UInt8)
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Option (List HiddenRecord) → Prop) :
    Config.Product.Returns (liftWG (messageEphemeral false e ck hash))
      (fun w => P w.wg w.fs w.tasks w.seccomp w.ambient.hidden)
      (fun out w => out = (first ck e, noiseHash (hash ++ e)) ∧
        P w.wg w.fs w.tasks w.seccomp w.ambient.hidden) := by
  intro w pre
  simp [messageEphemeral, kdf, kdf_single, kdfOut]
  refine ⟨_, _, _, rfl, ?_⟩
  exact ⟨⟨rfl, rfl⟩, pre⟩

theorem dh_returns (ck secret pub : List UInt8)
    (ok : (curve25519 secret pub).2 = true)
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Option (List HiddenRecord) → Prop) :
    Config.Product.Returns (liftWG (mixDh true ck secret pub))
      (fun w => P w.wg w.fs w.tasks w.seccomp w.ambient.hidden)
      (fun out w => out = some (first ck (curve25519 secret pub).1,
        second ck (curve25519 secret pub).1) ∧
        P w.wg w.fs w.tasks w.seccomp w.ambient.hidden) := by
  intro w pre
  simp [mixDh, ok, kdf, kdf_pair, kdfOut]
  refine ⟨_, _, rfl, ?_⟩
  exact ⟨rfl, pre⟩

theorem precomputed_returns (ck precomputed : List UInt8)
    (ok : precomputed ≠ List.replicate 32 0)
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Option (List HiddenRecord) → Prop) :
    Config.Product.Returns (liftWG (mixPrecomputedDh ck precomputed))
      (fun w => P w.wg w.fs w.tasks w.seccomp w.ambient.hidden)
      (fun out w => out = some (first ck precomputed, second ck precomputed) ∧
        P w.wg w.fs w.tasks w.seccomp w.ambient.hidden) := by
  intro w pre
  have nonzero : (precomputed == (noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.zeroKey)) = false := by
    change (precomputed == List.replicate 32 0) = false
    exact beq_eq_false_iff_ne.mpr ok
  simp [mixPrecomputedDh, nonzero, kdf, kdf_pair, kdfOut]
  refine ⟨_, _, rfl, ?_⟩
  exact ⟨rfl, pre⟩

theorem public_returns (secret : List UInt8) (nonnull : secret ≠ nullPoint)
    (ok : (curve25519 secret basePoint).2 = true)
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Option (List HiddenRecord) → Prop) :
    Config.Product.Returns (liftWG (generatePublic secret))
      (fun w => P w.wg w.fs w.tasks w.seccomp w.ambient.hidden)
      (fun out w => out = (some (curve25519 secret basePoint).1, true) ∧
        P w.wg w.fs w.tasks w.seccomp w.ambient.hidden) := by
  intro w pre
  have nonzero : (secret == nullPoint) = false := beq_eq_false_iff_ne.mpr nonnull
  simp only [generatePublic, nonzero, ok]
  refine ⟨_, _, rfl, ?_⟩
  exact ⟨rfl, pre⟩

end Leanux.Proofs.WG.Noise.InitiationReady
