import Leanux.Proofs.WG.Config.Returns
import Leanux.Proofs.WG.Config.Port

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem socketReinit_returns (new4 new6 : Option Nat) (d : Device) :
    Returns (socketReinit new4 new6) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some
        { d with sock4 := new4, sock6 := new6, incomingPort := new4.getD d.incomingPort }) := by
  rw [returns_iff]
  cases new4 <;> simp only [socketReinit, Option.isSome_some, Option.isSome_none,
    Option.getD_none, Option.getD_some]
  all_goals mvcgen [sockFree, iputReport, branch,
    getDev, getK, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals grind only

theorem socketInit_nonzero_returns (port : Nat) (nonzero : port ≠ 0)
    (d : Device) (bound : Bool) (net : d.creatingNet = true) :
    Returns (socketInit port) (fun w => w.k.wg = some d ∧ w.portBound port = bound)
      (fun ret w => if bound || d.sock4 == some port || d.sock6 == some port
        then ret = -EADDRINUSE ∧ w.k.wg = some d
        else ret = 0 ∧ w.k.wg = some
          { d with sock4 := some port, sock6 := some port, incomingPort := port }) := by
  have hs := (returns_iff _ _ _).mp (socketReinit_returns (some port) (some port) d)
  rw [returns_iff]
  simp [socketInit, nonzero]
  mvcgen [getDev, getK, iputReport, branch, invariant, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals grind only

end Leanux.Proofs.WG.Config
