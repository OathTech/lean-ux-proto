import Leanux.Proofs.WG.Roaming.InitiationModel
import Leanux.Proofs.WG.Roaming.ResponseCryptoEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

theorem initiationKdf_two (ck input : List UInt8) :
    kdfOutputs ck input 2 = [responseFirst ck input, responseSecond ck input] := by
  simp [kdfOutputs, responseFirst, responseSecond, List.range']


end Leanux.Proofs.WG.Roaming
