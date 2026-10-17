import Leanux.Proofs.WG.Roaming.ResponseModel
import Leanux.Proofs.WG.Noise.Basic

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

theorem responseKdf_one (ck input : List UInt8) :
    kdfOutputs ck input 1 = [responseFirst ck input] := by
  simp [kdfOutputs, responseFirst]
theorem responseKdf_three (ck input : List UInt8) :
    kdfOutputs ck input 3 = [responseFirst ck input, responseSecond ck input,
      responseThird ck input] := by
  simp [kdfOutputs, responseFirst, responseSecond, responseThird, List.range']

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
