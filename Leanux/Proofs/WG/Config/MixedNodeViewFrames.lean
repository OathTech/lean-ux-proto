import Leanux.Proofs.WG.Config.MixedNodeViewModel
import Leanux.Proofs.WG.Config.MixedGetterModel
import Leanux.Proofs.WG.Config.MixedPagePlanModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- A node's stored width, bits and CIDR determine its exact native dump cost
and JSON, including masking and non-32-width serialization. -/
theorem dumpNode_view_congr (n value : AipNode) (same : dumpNodeView value = dumpNodeView n) :
    dumpNodeSpace value = dumpNodeSpace n ∧ dumpNodeJson value = dumpNodeJson n := by
  have detail : value.bitlen = n.bitlen ∧ value.bits = n.bits ∧ value.cidr = n.cidr := by
    simpa only [dumpNodeView,Prod.mk.injEq] using same
  simp only [dumpNodeSpace,dumpNodeJson,detail.1,detail.2.1,detail.2.2,and_self]

/-- Exact sizing and serialization retain every supplied node occurrence. -/
theorem dumpNodes_view_congr (nodes values : NodeId → AipNode)
    (same : ∀ id, dumpNodeView (values id) = dumpNodeView (nodes id)) (ids : List NodeId) :
    dumpNodesSpace values ids = dumpNodesSpace nodes ids ∧
      dumpNodeJsons values ids = dumpNodeJsons nodes ids := by
  have sizes (id : NodeId) := (dumpNode_view_congr (nodes id) (values id) (same id)).1
  have json (id : NodeId) := (dumpNode_view_congr (nodes id) (values id) (same id)).2
  simp only [dumpNodesSpace,dumpNodeJsons,sizes,json,and_self]

/-- The exact greedy prefix depends on stored node widths, independently of
ownership and parent-link mutations. -/
theorem weightedPrefix_node_congr (nodes values : NodeId → AipNode)
    (same : ∀ id, dumpNodeView (values id) = dumpNodeView (nodes id))
    (room : Nat) (ids : List NodeId) :
    weightedPrefix values room ids = weightedPrefix nodes room ids := by
  induction ids generalizing room with
  | nil => rfl
  | cons id ids ih =>
    have size := (dumpNode_view_congr (nodes id) (values id) (same id)).1
    simp only [weightedPrefix,size]
    split
    · rw [ih]
    · rfl

/-- Full arbitrary-room peer serialization is unchanged, including exact
cancelled buffers, context initialization and complete/split attributes. -/
theorem weightedPeerResult_node_congr (d : Device) (nodes values : NodeId → AipNode)
    (same : ∀ id, dumpNodeView (values id) = dumpNodeView (nodes id))
    (p : Peer) (ctx : DumpCtx) (skb : NlSkb) (ids : List NodeId) :
    weightedPeerResult d values p ctx skb ids = weightedPeerResult d nodes p ctx skb ids := by
  have sizes (ids : List NodeId) := (dumpNodes_view_congr nodes values same ids).1
  have json (ids : List NodeId) := (dumpNodes_view_congr nodes values same ids).2
  simp only [weightedPeerResult,weightedAllowedResult,
    weightedPrefix_node_congr nodes values same,sizes,json]

/-- Preserve the complete scan result and its exact remaining occurrence
suffix, with no space, readability or execution-success premise. -/
theorem mixedPeerScan_node_congr (d : Device) (peers : PeerId → Peer)
    (nodes values : NodeId → AipNode)
    (same : ∀ id, dumpNodeView (values id) = dumpNodeView (nodes id))
    (rows : List MixedPeerRow) (ctx : DumpCtx) (cursor : Option PeerId)
    (skb : NlSkb) (prior : Array PeerDumpAttrs) :
    mixedPeerScan d peers values rows ctx cursor skb prior =
      mixedPeerScan d peers nodes rows ctx cursor skb prior := by
  induction rows generalizing ctx cursor skb prior with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨pid,ids⟩ := row
    simp only [mixedPeerScan,weightedPeerResult_node_congr d nodes values same]
    split
    · exact ih _ _ _ _
    · simp only [mixedPeerRemaining,weightedPrefix_node_congr nodes values same]
    · rfl

/-- Static first-head readiness is invariant under node-view preservation. -/
theorem mixedPageReady_node_congr (d : Device) (peers : PeerId → Peer)
    (nodes values : NodeId → AipNode)
    (same : ∀ id, dumpNodeView (values id) = dumpNodeView (nodes id))
    (rows : List MixedPeerRow) (ctx : DumpCtx) :
    MixedPageReady d peers values rows ctx ↔ MixedPageReady d peers nodes rows ctx := by
  have sizes (id : NodeId) := (dumpNode_view_congr (nodes id) (values id) (same id)).1
  simp only [MixedPageReady,mixedPeerHeadFits,sizes]

/-- Every planned page, native tuple and remaining suffix is unchanged.
This transports the full plan without identifying the underlying node stores. -/
theorem mixedPages_node_congr (d : Device) (peers : PeerId → Peer)
    (nodes values : NodeId → AipNode)
    (same : ∀ id, dumpNodeView (values id) = dumpNodeView (nodes id))
    (rows : List MixedPeerRow) (ctx : DumpCtx)
    (ready : MixedPageReady d peers nodes rows ctx)
    (currentReady : MixedPageReady d peers values rows ctx) :
    mixedPages d peers values rows ctx currentReady = mixedPages d peers nodes rows ctx ready := by
  let result := mixedPeerScan d peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[]
  have scan : mixedPeerScan d peers values rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[] = result :=
    mixedPeerScan_node_congr d peers nodes values same rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[]
  rw [mixedPages,mixedPages]
  simp only [scan]
  split
  next finished => rfl
  next unfinished => exact congrArg (List.cons result) (mixedPages_node_congr d peers nodes values same
    result.remaining {result.native.1 with nextPeer := result.native.2.1} _ _)
termination_by mixedPageMeasure rows ctx
decreasing_by
  apply mixedPageReady_progress d peers nodes rows ctx ready
  assumption

/-- The full mixed getter's canonical JSON retains every peer/node occurrence
when only non-serialized node metadata changes. -/
theorem mixedGetterJson_node_congr (d : Device) (peers : PeerId → Peer)
    (nodes values : NodeId → AipNode)
    (same : ∀ id, dumpNodeView (values id) = dumpNodeView (nodes id)) :
    mixedGetterJson d peers values = mixedGetterJson d peers nodes := by
  have json (ids : List NodeId) := (dumpNodes_view_congr nodes values same ids).2
  simp only [mixedGetterJson,mixedRowsParts,json]

end Leanux.Proofs.WG.Config
