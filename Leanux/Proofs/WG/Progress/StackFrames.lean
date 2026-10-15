import Leanux.Proofs.WG.Progress.ScheduleTurn

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Noise Std.Do

theorem hasWork_world (a : Activation) (initial : World) :
    Ensures (Activation.hasWork a) (fun w => w = initial) (fun _ w => w = initial) := by
  rw [ensures_iff]
  mvcgen [Activation.hasWork, getDev, getPeer, getTxSkb, getK, invariant]
  all_goals simp_all

end Leanux.Proofs.WG.Progress
