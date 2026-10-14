import Leanux.Proofs.WG.Config.Validation
import Leanux.Proofs.WG.Roaming.Basic

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def portState (k : Kernel) : Option (Nat × Option Nat × Option Nat × Bool) :=
  k.wg.map fun d => (d.incomingPort, d.sock4, d.sock6, d.running)

theorem clearPeerEndpointSrc_port_spec (pid : PeerId)
    (initial : Option (Nat × Option Nat × Option Nat × Bool)) :
    ⦃fun w => ⌜portState w.k = initial⌝⦄ clearPeerEndpointSrc pid
    ⦃⇓? _ w => ⌜portState w.k = initial⌝⦄ := by
  have hh := Roaming.hiddenJiffies_kernel_spec (fun k => portState k = initial)
  mvcgen [clearPeerEndpointSrc, dstCacheResetNow, dstCacheReset, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, invariant, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals try simp_all [portState, Option.map_map, Function.comp_def]
  all_goals subst_vars
  all_goals try simp_all [portState, Option.map_map, Function.comp_def]

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
