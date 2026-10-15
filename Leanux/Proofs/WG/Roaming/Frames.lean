import Leanux.Proofs.WG.Roaming.EndpointSource
import Leanux.Proofs.WG.Roaming.Model
import Leanux.Proofs.WG.Noise.KernelFrames

set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def destinationAt (k : Kernel) (pid : PeerId) : Option (Nat × Nat × Nat × Nat) :=
  ((k.wg.bind fun d => d.peers[pid]?).bind Peer.endpoint).map destination

theorem hiddenJiffies_kernel_spec (P : Kernel → Prop) (site : HiddenSite) :
    ⦃fun w => ⌜P w.k⌝⦄ hiddenJiffies site ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  have hh := hidden_kernel_spec P
  mvcgen [hiddenJiffies, hh]

theorem dstCacheReset_destination (pid : PeerId) (remote : Option (Nat × Nat × Nat × Nat)) :
    ⦃fun w => ⌜destinationAt w.k pid = remote⌝⦄ dstCacheReset pid
    ⦃⇓? _ w => ⌜destinationAt w.k pid = remote⌝⦄ := by
  have hh := hiddenJiffies_kernel_spec (fun k => destinationAt k pid = remote)
  mvcgen [dstCacheReset, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [destinationAt, Option.bind_map, Function.comp_def, Std.TreeMap.getElem?_insert]


end Leanux.Proofs.WG.Roaming
