import Leanux.Proofs.WG.Roaming.ResponseModel
import Leanux.Proofs.WG.Noise.Basic
import Leanux.Proofs.WG.Noise.KernelFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem responseKdf_one (ck input : List UInt8) :
    kdfOutputs ck input 1 = [responseFirst ck input] := by
  simp [kdfOutputs, responseFirst, List.range']
theorem responseKdf_three (ck input : List UInt8) :
    kdfOutputs ck input 3 = [responseFirst ck input, responseSecond ck input,
      responseThird ck input] := by
  simp [kdfOutputs, responseFirst, responseSecond, responseThird, List.range']

theorem responseKdf_one_returns (ck input : List UInt8) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ kdf false false ck input
      ⦃⇓ outs w => ⌜outs = [responseFirst ck input] ∧ P w.k⌝⦄ := by
  mvcgen [kdf, WG.orM, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [responseKdf_one]

theorem responseKdf_three_returns (ck input : List UInt8) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ kdf true true ck input
      ⦃⇓ outs w => ⌜outs = [responseFirst ck input, responseSecond ck input,
        responseThird ck input] ∧ P w.k⌝⦄ := by
  mvcgen [kdf, WG.orM, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [responseKdf_three]

theorem responseEphemeral_returns (e ck hash : List UInt8) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ messageEphemeral true e ck hash
      ⦃⇓ out w => ⌜out = (responseFirst ck e, noiseHash (hash ++ e)) ∧ P w.k⌝⦄ := by
  have hk := responseKdf_one_returns ck e P
  mvcgen [messageEphemeral, kdfOut, branch, invariant, hk]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem responseDh_returns (ck priv pub : List UInt8) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ mixDh false ck priv pub
      ⦃⇓ out w => ⌜P w.k ∧ ∀ result, out = some result →
        (curve25519 priv pub).2 = true ∧
        result = (responseFirst ck (curve25519 priv pub).1, [])⌝⦄ := by
  have hk := responseKdf_one_returns ck (curve25519 priv pub).1 P
  mvcgen [mixDh, kdfOut, branch, invariant, hk]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals grind

theorem responseDecrypt_returns (sealed key hash : List UInt8) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ messageDecrypt sealed key hash
      ⦃⇓ out w => ⌜P w.k ∧ ∀ result, out = some result →
        aeadDecrypt key noiseNonce sealed hash = some result.1 ∧
        result.2 = noiseHash (hash ++ sealed)⌝⦄ := by
  cases dec : aeadDecrypt key noiseNonce sealed hash <;>
    mvcgen [messageDecrypt, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals grind

/-- A successful response decrypt has empty plaintext because its sealed input
contains at most the tag's sixteen bytes; no full-message length premise is used. -/
theorem responseDecrypt_empty (msg key aad plain : List UInt8)
    (ok : aeadDecrypt key noiseNonce ((msg.drop 44).take 16) aad = some plain) :
    plain = [] := by
  have len : ((msg.drop 44).take 16).length ≤ 16 := List.length_take_le _ _
  simp only [aeadDecrypt] at ok
  split at ok <;> try contradiction
  have zero : ((msg.drop 44).take 16).length - 16 = 0 := by omega
  simp only [zero, List.take_zero] at ok
  split at ok <;> try contradiction
  simpa [chacha20] using (Option.some.inj ok).symm

end Leanux.Proofs.WG.Roaming
