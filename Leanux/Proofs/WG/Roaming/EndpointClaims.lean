import Leanux.Proofs.WG.Roaming.Frames

set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

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
