import Leanux.Proofs.WG.Config.CollisionRemovalModel
import Leanux.Proofs.WG.Config.QuietRemoval

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem removalDeadGuard_device (pid : PeerId) (d : Device) :
    Ensures (removalDeadGuard pid) (fun w => w.dev = some d)
      (fun _ w => w.dev = some d) := by
  intro g ambient result final after device run
  cases resident : d.peers[pid]? with
  | none => simp [removalDeadGuard, getPeer, getDev, device, resident, invariant, AmbientM.invariant] at run; cases run
  | some p =>
    cases dead : p.isDead <;>
      simp [removalDeadGuard, getPeer, getDev, device, resident, dead,
        branch, AmbientM.branch, unsupported, AmbientM.unsupported] at run
    · cases run
    · rcases run with ⟨⟨rfl, rfl⟩, rfl⟩; exact device

end Leanux.Proofs.WG.Config
