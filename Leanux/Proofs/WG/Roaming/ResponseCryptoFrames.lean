import Leanux.Proofs.WG.Roaming.ResponseCryptoEffects
import Leanux.Proofs.WG.Config.Returns

/-! Exact crypto results together with preservation of all former Kernel
owners through the actual product lift. Ambient decision traces may change. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

theorem responseKdf_one_returns (ck input : List UInt8)
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) :
    Config.Product.Returns (liftWG (kdf false false ck input))
      (fun w => P w.wg w.fs w.tasks w.seccomp)
      (fun outs w => outs = [responseFirst ck input] ∧ P w.wg w.fs w.tasks w.seccomp) := by
  intro w pre
  refine ⟨_, _, rfl, ?_⟩
  exact ⟨by simp [responseKdf_one], pre⟩

theorem responseKdf_three_returns (ck input : List UInt8)
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) :
    Config.Product.Returns (liftWG (kdf true true ck input))
      (fun w => P w.wg w.fs w.tasks w.seccomp)
      (fun outs w => outs = [responseFirst ck input, responseSecond ck input,
        responseThird ck input] ∧ P w.wg w.fs w.tasks w.seccomp) := by
  intro w pre
  refine ⟨_, _, rfl, ?_⟩
  exact ⟨responseKdf_three ck input, pre⟩

theorem responseEphemeral_returns (e ck hash : List UInt8)
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) :
    Config.Product.Returns (liftWG (messageEphemeral true e ck hash))
      (fun w => P w.wg w.fs w.tasks w.seccomp)
      (fun out w => out = (responseFirst ck e, noiseHash (hash ++ e)) ∧
        P w.wg w.fs w.tasks w.seccomp) := by
  intro w pre
  simp [messageEphemeral, kdf, responseKdf_one, kdfOut]
  refine ⟨_, _, _, rfl, ?_⟩
  exact ⟨⟨rfl, rfl⟩, pre⟩

theorem responseDh_returns (ck priv pub : List UInt8)
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) :
    Config.Product.Returns (liftWG (mixDh false ck priv pub))
      (fun w => P w.wg w.fs w.tasks w.seccomp)
      (fun out w => P w.wg w.fs w.tasks w.seccomp ∧ ∀ result, out = some result →
        (curve25519 priv pub).2 = true ∧
        result = (responseFirst ck (curve25519 priv pub).1, [])) := by
  intro w pre
  cases ok : (curve25519 priv pub).2 with
  | false =>
    simp [mixDh, ok]
    refine ⟨_, _, rfl, pre, ?_⟩
    simp
  | true =>
    simp [mixDh, ok, kdf, responseKdf_one, kdfOut]
    refine ⟨_, _, rfl, pre, ?_⟩
    simp_all

theorem responseDecrypt_returns (sealed key hash : List UInt8)
    (P : WGWorld → FSWorld → TaskWorld → SeccompWorld → Prop) :
    Config.Product.Returns (liftWG (messageDecrypt sealed key hash))
      (fun w => P w.wg w.fs w.tasks w.seccomp)
      (fun out w => P w.wg w.fs w.tasks w.seccomp ∧ ∀ result, out = some result →
        aeadDecrypt key noiseNonce sealed hash = some result.1 ∧
        result.2 = noiseHash (hash ++ sealed)) := by
  intro w pre
  cases dec : aeadDecrypt key noiseNonce sealed hash with
  | none =>
    simp [messageDecrypt, dec]
    refine ⟨_, _, rfl, pre, ?_⟩
    simp
  | some plain =>
    simp [messageDecrypt, dec]
    refine ⟨_, _, rfl, pre, ?_⟩
    simp_all

end Leanux.Proofs.WG.Roaming
