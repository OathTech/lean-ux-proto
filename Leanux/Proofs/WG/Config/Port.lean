import Leanux.Proofs.WG.Config.OperationFrames
import Leanux.Proofs.WG.Config.Validation
import Leanux.Proofs.WG.Roaming.Basic

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem setPort_down (port old : Nat) (sock4 sock6 : Option Nat) :
    Ensures (setPort port)
      (fun w => portState w.k = some (old, sock4, sock6, false))
      (fun ret w => ret = 0 ∧ portState w.k = some (port, sock4, sock6, false)) := by
  rw [ensures_iff]
  have hc := fun pid => clearPeerEndpointSrc_port_spec pid (some (old, sock4, sock6, false))
  have hs := unconstrained_prefix (socketInit port)
  mvcgen [setPort, getDev, getK, modifyDev, modifyK, branch, invariant, hc, hs]
  invariants
  | inv1 => ((⇓? _ w => ⌜portState w.k = some (old, sock4, sock6, false)⌝) :
      PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [portState, Option.map_map, Function.comp_def]
  all_goals subst_vars
  all_goals try simp_all [portState, Option.map_map, Function.comp_def]
  all_goals grind only

end Leanux.Proofs.WG.Config
