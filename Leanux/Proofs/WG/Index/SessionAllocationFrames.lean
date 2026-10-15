import Leanux.Proofs.WG.Noise.RotationModel
import Leanux.Proofs.WG.Index.StoreFieldFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

theorem clearPut_allocation_cursor {key : Option KeypairId} {d final : Device}
    (run : ClearPut key d final) : final.nextKeypairId = d.nextKeypairId := by
  cases run with
  | null => rfl
  | present d id k resident live word => exact released_next d id k true

theorem rotationRun_allocation_cursor {pid : PeerId} {d final : Device}
    {actions : List RotationAction} (run : RotationRun pid d actions final) :
    final.nextKeypairId = d.nextKeypairId := by
  induction run with
  | nil => rfl
  | write d final change p rest resident tail ih => exact ih
  | put d middle final key rest release tail ih =>
    exact ih.trans (clearPut_allocation_cursor release)

end Leanux.Proofs.WG.Index
