import Leanux.Proofs.WG.Noise.ClearModel
import Leanux.Proofs.WG.Index.ReleaseEffects

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

theorem clearPut_peers {key : Option KeypairId} {d final : Device}
    (put : ClearPut key d final) : final.peers = d.peers := by
  cases put with
  | null => rfl
  | present d id k resident live word =>
    by_cases last : k.refcount = 1 <;> simp [Index.releasedDevice, Index.unhashKeypair, last]

end Leanux.Proofs.WG.Noise
