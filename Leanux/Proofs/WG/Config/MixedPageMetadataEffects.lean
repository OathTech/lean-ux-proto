import Leanux.Proofs.WG.Config.MixedPagePlanModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Serializer metadata preservation, including cancellation. -/
theorem weightedPeerResult_metadata (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb : NlSkb) (ids : List NodeId)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq) :
    let out := weightedPeerResult d nodes p ctx skb ids
    out.2.1.hasWg = ctx.hasWg ∧
      (out.2.1.allowedipsSeq = 0 ∨ out.2.1.allowedipsSeq = d.peerAllowedips.seq) ∧
      out.1.messages = skb.messages := by
  let cost := if ctx.nextAllowedip.isNone then peerFixedSpace p else 40
  by_cases fits : cost ≤ skb.room
  · simp only [weightedPeerResult,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40) = cost from rfl,
      ite_eq_left fits]
    cases ids with
    | nil => simp [weightedAllowedResult]
    | cons first ids =>
      by_cases nest : skb.room-cost < 4
      · simp [weightedAllowedResult,nest]
      · simp only [weightedAllowedResult,ite_eq_right nest]
        cases plan : weightedPrefix nodes (skb.room-cost-4) (first::ids) with
        | mk front remaining => cases remaining <;> simp
  · simp only [weightedPeerResult,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40) = cost from rfl,
      ite_eq_right fits]
    simpa using sequence

/-- The scan preserves hasWg, the valid sequence domain and existing messages. -/
theorem mixedPeerScan_metadata (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (rows : List MixedPeerRow) (ctx : DumpCtx)
    (cursor : Option PeerId) (skb : NlSkb) (prior : Array PeerDumpAttrs)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq) :
    let out := mixedPeerScan d peers nodes rows ctx cursor skb prior
    out.native.1.hasWg = ctx.hasWg ∧
      (out.native.1.allowedipsSeq = 0 ∨ out.native.1.allowedipsSeq = d.peerAllowedips.seq) ∧
      out.native.2.2.1.messages = skb.messages := by
  induction rows generalizing ctx cursor skb prior with
  | nil => exact ⟨rfl,sequence,rfl⟩
  | cons row rows ih =>
    obtain ⟨pid,ids⟩ := row
    have one := weightedPeerResult_metadata d nodes (peers pid) ctx skb ids sequence
    cases outcome : weightedPeerResult d nodes (peers pid) ctx skb ids with
    | mk out rest =>
      obtain ⟨after,verdict⟩ := rest
      rw [outcome] at one
      dsimp only at one
      cases verdict with
      | complete attrs =>
        have tail := ih after (some pid) out (prior.push attrs) one.2.1
        simp only [mixedPeerScan,outcome]
        exact ⟨tail.1.trans one.1,tail.2.1,tail.2.2.trans one.2.2⟩
      | split attrs => simpa only [mixedPeerScan,outcome] using one
      | cancelled => simpa only [mixedPeerScan,outcome] using one

/-- Every planned page retains hasWg, the permitted sequence domain and its
initially empty message buffer. -/
theorem mixedPages_metadata (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (ready : MixedPageReady d peers nodes rows ctx)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq) :
    ∀ page ∈ mixedPages d peers nodes rows ctx ready,
      page.native.1.hasWg = ctx.hasWg ∧
      (page.native.1.allowedipsSeq = 0 ∨ page.native.1.allowedipsSeq = d.peerAllowedips.seq) ∧
      page.native.2.2.1.messages = [] := by
  let result := mixedPeerScan d peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[]
  have one := mixedPeerScan_metadata d peers nodes rows ctx ctx.nextPeer
    {room := mixedPageRoom d ctx} #[] sequence
  change result.native.1.hasWg = ctx.hasWg ∧ _ at one
  intro page member
  rw [mixedPages] at member
  dsimp only at member
  by_cases finished : result.remaining = []
  · rw [dite_eq_left finished] at member
    simp only [List.mem_singleton] at member
    subst page
    exact one
  · rw [dite_eq_right finished] at member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact one
    · have later := mixedPages_metadata d peers nodes result.remaining
        {result.native.1 with nextPeer := result.native.2.1}
        (mixedPageReady_next d peers nodes rows ctx ready finished) one.2.1 page member
      exact ⟨later.1.trans one.1,later.2⟩
termination_by mixedPageMeasure rows ctx
decreasing_by exact mixedPageReady_progress d peers nodes rows ctx ready finished

end Leanux.Proofs.WG.Config
