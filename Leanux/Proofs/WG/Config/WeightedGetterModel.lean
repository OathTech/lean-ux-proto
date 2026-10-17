import Leanux.Proofs.WG.Config.WeightedStartModel
import Leanux.Proofs.WG.Config.GenericPaginationModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Actual receives for the resumed DATA pages, with one extra envelope only
when the final DATA page leaves insufficient room for DONE. -/
def weightedTailReceives (d : Device) (nodes : NodeId → AipNode) : List (List NodeId) → Nat
  | [] => 0
  | page :: pages => if pages.isEmpty then
      if NLMSG_GOODSIZE - (devicePrefixSpace d + 44 + dumpNodesSpace nodes page) < nlmsgTotal 4
      then 2 else 1
    else 1 + weightedTailReceives d nodes pages

/-- Count the original DATA receives and possible final DONE spill. Empty
input is one fixed-attribute DATA page; an empty first prefix still precedes
the nonempty resumed pages. -/
def weightedGetterReceives (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (ids : List NodeId) : Nat :=
  let result := weightedPrefix nodes (NLMSG_GOODSIZE - devicePrefixSpace d - (peerFixedSpace p+4)) ids
  if result.2.isEmpty then
    if (mixedFirstCall d p nodes ids).skb.room < nlmsgTotal 4 then 2 else 1
  else 1 + weightedTailReceives d nodes
    (weightedTailPages nodes (NLMSG_GOODSIZE - devicePrefixSpace d - 44) result.2)

/-- Resumed planning uses exactly the same greedy prefix once its first node
fits. The definition's unconditional head-consumption is justified here. -/
theorem weightedTailPages_prefix (nodes : NodeId → AipNode) (room : Nat)
    (start : NodeId) (rest : List NodeId) (enough : 40 ≤ room) :
    weightedTailPages nodes room (start::rest) =
      (weightedPrefix nodes room (start::rest)).1 ::
        weightedTailPages nodes room (weightedPrefix nodes room (start::rest)).2 := by
  have fits : dumpNodeSpace (nodes start) ≤ room := Nat.le_trans (dumpNodeSpace_bounds _).2 enough
  rw [weightedTailPages,weightedPrefix,ite_eq_left fits]

/-- Exact raw DATA messages followed by DONE. An empty input omits the raw
allowed-IP attribute, unlike a nonempty input whose first prefix is empty. -/
def weightedGetterMessages (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (ids : List NodeId) : List NlMessage :=
  match ids with
  | [] => [.data 2 (deviceFixedAttrs d)
      (some [{publicKey := hexKey p.remoteStatic,attrs := peerFixedAttrs p}]), .done 2 0]
  | first::rest =>
    let result := weightedPrefix nodes (NLMSG_GOODSIZE-devicePrefixSpace d-(peerFixedSpace p+4)) (first::rest)
    jsonPaginationMessages d p (result.1.map (fun id => dumpNodeJson (nodes id)))
      ((weightedTailPages nodes (NLMSG_GOODSIZE-devicePrefixSpace d-44) result.2).map
        (fun page => page.map (fun id => dumpNodeJson (nodes id))))

/-- Every resumed boundary is absent from the complete previously emitted prefix. -/
def weightedGetterFresh (d : Device) (p : Peer) (nodes : NodeId → AipNode) (ids : List NodeId) : Prop :=
  let result := weightedPrefix nodes (NLMSG_GOODSIZE-devicePrefixSpace d-(peerFixedSpace p+4)) ids
  weightedBoundaryFresh result.1
    (weightedTailPages nodes (NLMSG_GOODSIZE-devicePrefixSpace d-44) result.2)

end Leanux.Proofs.WG.Config
