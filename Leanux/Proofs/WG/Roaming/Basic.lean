import Leanux.Proofs.WG.Noise.KernelFrames

set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The remote destination, excluding cached local source information and
IPv6 flowinfo, which endpoint_eq intentionally does not compare. -/
def destination (e : Endpoint) : Nat × Nat × Nat × Nat :=
  (e.family, e.addr, e.port, if e.family = AF_INET6 then e.scope else 0)

def destinationAt (k : Kernel) (pid : PeerId) : Option (Nat × Nat × Nat × Nat) :=
  ((k.wg.bind fun d => d.peers[pid]?).bind Peer.endpoint).map destination

def sourceEndpoint (src : SkbSource) : Endpoint :=
  if src.family = 4 then
    { family := AF_INET, addr := src.saddr, port := src.sport, src := src.daddr, srcIf := src.iif }
  else
    { family := AF_INET6, addr := src.saddr, port := src.sport, src := src.daddr,
      scope := if src.saddr / 2 ^ 118 = 0x3fa then src.iif else 0 }

theorem endpointFromSkb_exact (src : SkbSource) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ endpointFromSkb src
    ⦃⇓? result w => ⌜P w.k ∧ result = some (sourceEndpoint src) ∧
      (src.family = 4 ∨ src.family = 6)⌝⦄ := by
  mvcgen [endpointFromSkb, branch, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [sourceEndpoint]

theorem endpointEq_destination (P : Kernel → Prop) (a : Endpoint) (b : Option Endpoint)
    (valid : a.family = AF_INET ∨ a.family = AF_INET6) :
    ⦃fun w => ⌜P w.k⌝⦄ endpointEq a b
    ⦃⇓? ok w => ⌜P w.k ∧ (ok = true → b.map destination = some (destination a))⌝⦄ := by
  mvcgen [endpointEq, Leanux.WG.andM, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals cases b <;> simp_all [destination, AF_INET, AF_INET6]
  all_goals grind

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

theorem setPeerEndpoint_destination (pid : PeerId) (e : Endpoint)
    (valid : e.family = AF_INET ∨ e.family = AF_INET6) :
    Ensures (setPeerEndpoint pid e) (fun _ => True)
      (fun _ w => destinationAt w.k pid = some (destination e)) := by
  rw [ensures_iff]
  have he := fun b => endpointEq_destination (fun k => destinationAt k pid = b.map destination) e b valid
  have hc := dstCacheReset_destination pid (some (destination e))
  mvcgen [setPeerEndpoint, requireNotPending, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, branch, invariant, he, hc]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [destinationAt, Option.bind_map, Function.comp_def, Std.TreeMap.getElem?_insert]
  all_goals grind

theorem clearPeerEndpointSrc_destination (pid : PeerId) (remote : Option (Nat × Nat × Nat × Nat)) :
    Ensures (clearPeerEndpointSrc pid) (fun w => destinationAt w.k pid = remote)
      (fun _ w => destinationAt w.k pid = remote) := by
  rw [ensures_iff]
  have hc := dstCacheReset_destination pid remote
  mvcgen [clearPeerEndpointSrc, dstCacheResetNow, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, invariant, hc]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [destinationAt, destination, Option.bind_map, Function.comp_def,
    Std.TreeMap.getElem?_insert, Option.map_map]
  all_goals assumption

theorem setPeerEndpointFromSkb_destination (pid : PeerId) (src : SkbSource) :
    Ensures (setPeerEndpointFromSkb pid src) (fun _ => True)
      (fun _ w => destinationAt w.k pid = some (destination (sourceEndpoint src))) := by
  rw [ensures_iff]
  have he := endpointFromSkb_exact src (fun _ => True)
  have hs := fun e h => (ensures_iff _ _ _).mp (setPeerEndpoint_destination pid e h)
  mvcgen [setPeerEndpointFromSkb, branch, invariant, he, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [sourceEndpoint]
  all_goals split <;> simp_all

end Leanux.Proofs.WG.Roaming
