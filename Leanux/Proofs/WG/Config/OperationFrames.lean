import Leanux.Proofs.WG.Config.Model
import Leanux.Proofs.WG.Config.BranchSource
import Leanux.Proofs.WG.Roaming.Frames

/-! Preservation support separated from configuration effects and public claims.
Delete structural frames made trivial by the subsystem split; keep meaningful
within-WireGuard preservation obligations. -/
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

theorem clearEndpointSource_device_frame (pid : PeerId) (initial : Option Device) :
    ⦃fun w => ⌜w.k.wg.map withoutPeers = initial⌝⦄ clearPeerEndpointSrc pid
    ⦃⇓? _ w => ⌜w.k.wg.map withoutPeers = initial⌝⦄ := by
  have hh := Roaming.hiddenJiffies_kernel_spec (fun k => k.wg.map withoutPeers = initial)
  mvcgen [clearPeerEndpointSrc, dstCacheResetNow, dstCacheReset,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [withoutPeers, Option.map_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all [withoutPeers, Option.map_map, Function.comp_def]

theorem clearEndpointSource_portBound (pid : PeerId) (bound : Nat → Bool) :
    Ensures (clearPeerEndpointSrc pid) (fun w => w.portBound = bound)
      (fun _ w => w.portBound = bound) := by
  have hh := hidden_portBound bound
  rw [ensures_iff]
  mvcgen [clearPeerEndpointSrc, dstCacheResetNow, dstCacheReset, hiddenJiffies,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant, hh]

end Leanux.Proofs.WG.Config
