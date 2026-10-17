import Leanux.Proofs.WG.Config.MixedGetterModel
import Leanux.Proofs.WG.Config.MixedPageDeviceModel
import Leanux.Proofs.WG.Config.MixedPagePlanModel
import Leanux.Proofs.WG.Config.PeerKeyGetterModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Static mixed-page readiness depends on the actual device header capacity
and peer serialization costs, not hidden handshake/index fields. -/
theorem mixedPageReady_getter_congr (d current : Device) (peers values : PeerId → Peer)
    (space : devicePrefixSpace current = devicePrefixSpace d)
    (same : ∀ q, keyGetterPeerView (values q) = keyGetterPeerView (peers q))
    (nodes : NodeId → AipNode) (rows : List MixedPeerRow) (ctx : DumpCtx) :
    MixedPageReady current values nodes rows ctx ↔ MixedPageReady d peers nodes rows ctx := by
  have cost (q : PeerId) : peerFixedSpace (values q) = peerFixedSpace (peers q) := by
    have view := same q
    simp only [keyGetterPeerView,Prod.mk.injEq] at view
    exact view.2.2.1
  simp only [MixedPageReady,mixedPageRoom,space,mixedPeerHeadFits,cost]

/-- Full canonical pages agree under their exact serializer inputs, including
all fragments, cancellation, repeated headers and final-room/DONE decisions. -/
theorem mixedPages_getter_congr (d current : Device) (peers values : PeerId → Peer)
    (space : devicePrefixSpace current = devicePrefixSpace d)
    (sequence : current.peerAllowedips.seq = d.peerAllowedips.seq)
    (same : ∀ q, keyGetterPeerView (values q) = keyGetterPeerView (peers q))
    (nodes : NodeId → AipNode) (rows : List MixedPeerRow) (ctx : DumpCtx)
    (ready : MixedPageReady d peers nodes rows ctx)
    (currentReady : MixedPageReady current values nodes rows ctx) :
    mixedPages current values nodes rows ctx currentReady = mixedPages d peers nodes rows ctx ready := by
  have serializer (q : PeerId) (ctx : DumpCtx) (skb : NlSkb) (ids : List NodeId) :
      weightedPeerResult current nodes (values q) ctx skb ids =
        weightedPeerResult d nodes (peers q) ctx skb ids := by
    have view := same q
    simp only [keyGetterPeerView,Prod.mk.injEq] at view
    simp only [weightedPeerResult,view.1,view.2.1,view.2.2.1,weightedAllowedResult,sequence]
  have scan (rows : List MixedPeerRow) (ctx : DumpCtx) (cursor : Option PeerId)
      (skb : NlSkb) (prior : Array PeerDumpAttrs) :
      mixedPeerScan current values nodes rows ctx cursor skb prior =
        mixedPeerScan d peers nodes rows ctx cursor skb prior := by
    induction rows generalizing ctx cursor skb prior with
    | nil => rfl
    | cons row rows ih =>
      obtain ⟨pid,ids⟩ := row
      have cost : peerFixedSpace (values pid) = peerFixedSpace (peers pid) := by
        have view := same pid
        simp only [keyGetterPeerView,Prod.mk.injEq] at view
        exact view.2.2.1
      simp only [mixedPeerScan,serializer]
      split
      · exact ih _ _ _ _
      · simp only [mixedPeerRemaining,cost]
      · rfl
  let result := mixedPeerScan d peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[]
  have currentEq : mixedPeerScan current values nodes rows ctx ctx.nextPeer
      {room := mixedPageRoom current ctx} #[] = result := by
    simpa only [result,mixedPageRoom,space] using scan rows ctx ctx.nextPeer
      {room := mixedPageRoom current ctx} #[]
  rw [mixedPages,mixedPages]
  simp only [currentEq]
  split
  next finished => rfl
  next unfinished => exact congrArg (List.cons result) (mixedPages_getter_congr d current peers values space sequence same nodes
      result.remaining {result.native.1 with nextPeer := result.native.2.1} _ _)
termination_by mixedPageMeasure rows ctx
decreasing_by
  apply mixedPageReady_progress d peers nodes rows ctx ready
  assumption

/-- Preserved device fields and resident peer views transport occurrence rows,
JSON, computed boundary freshness and cursor lifetime data without raw map equality. -/
theorem mixedGetter_data_congr (d current : Device) (peers values : PeerId → Peer)
    (members : current.peerList = d.peerList)
    (attrs : deviceFixedAttrs current = deviceFixedAttrs d)
    (same : ∀ q, keyGetterPeerView (values q) = keyGetterPeerView (peers q))
    (lookup : ∀ q : PeerId, (current.peers[q]?).map keyGetterPeerView = (d.peers[q]?).map keyGetterPeerView)
    (nodes : NodeId → AipNode) :
    mixedInitialRows current values = mixedInitialRows d peers ∧
    mixedGetterJson current values nodes = mixedGetterJson d peers nodes ∧
    (∀ pages, MixedPlanFresh current values pages ↔ MixedPlanFresh d peers pages) ∧
    (∀ pages, MixedPlanCursorData current pages ↔ MixedPlanCursorData d pages) := by
  have detail (q : PeerId) :
      (values q).remoteStatic = (peers q).remoteStatic ∧
      peerFixedAttrs (values q) = peerFixedAttrs (peers q) ∧
      peerFixedSpace (values q) = peerFixedSpace (peers q) ∧
      (values q).allowedipsList = (peers q).allowedipsList ∧
      (values q).refcount = (peers q).refcount ∧ (values q).isDead = (peers q).isDead := by
    simpa only [keyGetterPeerView,Prod.mk.injEq] using same q
  have rows : mixedInitialRows current values = mixedInitialRows d peers := by
    simp only [mixedInitialRows,members,(detail _).2.2.2.1]
  refine ⟨rows,?_,?_,?_⟩
  · simp only [mixedGetterJson,attrs,rows]
    congr 4
    cases shape : mixedInitialRows d peers with
    | nil => rfl
    | cons row rest =>
      simp only [mixedRowsParts,mixedPeerFixed,Option.isNone_none,ite_true,(detail _).1,(detail _).2.1]
  · intro pages
    simp only [MixedPlanFresh,MixedBoundaryFresh,members,(detail _).2.2.2.1]
  · have present (q : PeerId) (p : Peer) (resident : d.peers[q]? = some p) :
        ∃ next, current.peers[q]? = some next ∧ keyGetterPeerView next = keyGetterPeerView p := by
      apply Option.map_eq_some_iff.mp
      rw [lookup q,resident]
      rfl
    have original (q : PeerId) (p : Peer) (resident : current.peers[q]? = some p) :
        ∃ prior, d.peers[q]? = some prior ∧ keyGetterPeerView prior = keyGetterPeerView p := by
      apply Option.map_eq_some_iff.mp
      rw [← lookup q,resident]
      rfl
    intro pages
    constructor
    · intro data page member q selected
      obtain ⟨p,resident,live,positive,bound⟩ := data page member q selected
      obtain ⟨prior,found,view⟩ := original q p resident
      simp only [keyGetterPeerView,Prod.mk.injEq] at view
      exact ⟨prior,found,view.2.2.2.2.2.trans live,by simpa only [view.2.2.2.2.1] using positive,
        by simpa only [view.2.2.2.2.1] using bound⟩
    · intro data page member q selected
      obtain ⟨p,resident,live,positive,bound⟩ := data page member q selected
      obtain ⟨next,found,view⟩ := present q p resident
      simp only [keyGetterPeerView,Prod.mk.injEq] at view
      exact ⟨next,found,view.2.2.2.2.2.trans live,by simpa only [view.2.2.2.2.1] using positive,
        by simpa only [view.2.2.2.2.1] using bound⟩

end Leanux.Proofs.WG.Config
