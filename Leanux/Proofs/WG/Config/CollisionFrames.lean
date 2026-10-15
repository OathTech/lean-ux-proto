import Leanux.Proofs.WG.Config.CollisionModel
import Leanux.Proofs.WG.Config.QuietRemoval

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem removalDeadGuard_device (pid : PeerId) (d : Device) :
    Ensures (removalDeadGuard pid) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some d) := by
  rw [ensures_iff]
  mvcgen [removalDeadGuard, getPeer, getDev, getK, branch, invariant, unsupported]

end Leanux.Proofs.WG.Config
