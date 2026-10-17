import Leanux.Proofs.WG.Noise.InitiationReadyModel

/-! Pure output identities for the initiation's KDF calls. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.InitiationReady
open Leanux Leanux.WG

theorem kdf_pair (ck data : List UInt8) : kdfOutputs ck data 2 = [first ck data, second ck data] := by
  simp [kdfOutputs, first, second, List.range']
theorem kdf_single (ck data : List UInt8) : kdfOutputs ck data 1 = [first ck data] := by
  simp [kdfOutputs, first]

end Leanux.Proofs.WG.Noise.InitiationReady
