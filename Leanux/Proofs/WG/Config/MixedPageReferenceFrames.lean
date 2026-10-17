import Leanux.Proofs.WG.Config.MixedPagePlanClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Reference-only changes and an unchanged allowed-IP sequence preserve the
exact arbitrary-room peer result. -/
theorem weightedPeerResult_refcount (d current : Device)
    (sequence : current.peerAllowedips.seq = d.peerAllowedips.seq)
    (nodes : NodeId → AipNode) (p : Peer) (refs : Nat)
    (ctx : DumpCtx) (skb : NlSkb) (ids : List NodeId) :
    weightedPeerResult current nodes {p with refcount := refs} ctx skb ids =
      weightedPeerResult d nodes p ctx skb ids := by
  simp only [weightedPeerResult,peerFixedSpace,peerFixedAttrs,weightedAllowedResult,sequence]
  rfl

/-- The two-level scan ignores reference-only peer changes and other Device
fields once the allowed-IP sequence is fixed. -/
theorem mixedPeerScan_refcounts (d current : Device)
    (sequence : current.peerAllowedips.seq = d.peerAllowedips.seq)
    (peers : PeerId → Peer) (refs : PeerId → Nat) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (cursor : Option PeerId)
    (skb : NlSkb) (prior : Array PeerDumpAttrs) :
    mixedPeerScan current (fun id => {peers id with refcount := refs id}) nodes rows ctx cursor skb prior =
      mixedPeerScan d peers nodes rows ctx cursor skb prior := by
  induction rows generalizing ctx cursor skb prior with
  | nil => rfl
  | cons row rows ih =>
    rcases row with ⟨pid,ids⟩
    simp only [mixedPeerScan,weightedPeerResult_refcount d current sequence]
    split
    · exact ih _ _ _ _
    · rfl
    · rfl

/-- Room and fresh/resumed head-fit conditions ignore held references. -/
theorem mixedPageReady_refcounts (d current : Device)
    (space : devicePrefixSpace current = devicePrefixSpace d)
    (peers : PeerId → Peer) (refs : PeerId → Nat) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) :
    MixedPageReady current (fun id => {peers id with refcount := refs id}) nodes rows ctx ↔
      MixedPageReady d peers nodes rows ctx := by
  simp only [MixedPageReady,mixedPageRoom,space,mixedPeerHeadFits,peerFixedSpace]

/-- The complete planned page sequence is unchanged by reference-only peer
writes when its header size and allowed-IP sequence stay fixed. -/
theorem mixedPages_refcounts (d current : Device)
    (space : devicePrefixSpace current = devicePrefixSpace d)
    (sequence : current.peerAllowedips.seq = d.peerAllowedips.seq)
    (peers : PeerId → Peer) (refs : PeerId → Nat) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx)
    (ready : MixedPageReady d peers nodes rows ctx)
    (currentReady : MixedPageReady current (fun id => {peers id with refcount := refs id}) nodes rows ctx) :
    mixedPages current (fun id => {peers id with refcount := refs id}) nodes rows ctx currentReady =
      mixedPages d peers nodes rows ctx ready := by
  let result := mixedPeerScan d peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[]
  have same : mixedPeerScan current (fun id => {peers id with refcount := refs id}) nodes
      rows ctx ctx.nextPeer {room := mixedPageRoom current ctx} #[] = result := by
    simpa only [result,mixedPageRoom,space] using mixedPeerScan_refcounts d current sequence peers refs nodes
      rows ctx ctx.nextPeer {room := mixedPageRoom current ctx} #[]
  rw [mixedPages,mixedPages]
  simp only [same]
  split
  next finished => rfl
  next unfinished => exact congrArg (List.cons result) (mixedPages_refcounts d current space sequence peers refs nodes
      result.remaining {result.native.1 with nextPeer := result.native.2.1} _ _)
termination_by mixedPageMeasure rows ctx
decreasing_by
  apply mixedPageReady_progress d peers nodes rows ctx ready
  assumption

end Leanux.Proofs.WG.Config
