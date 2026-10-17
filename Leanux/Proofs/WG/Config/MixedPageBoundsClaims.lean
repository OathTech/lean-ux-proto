import Leanux.Proofs.WG.Config.MixedPageTransportModel
import Leanux.Proofs.WG.Config.MixedPageMetadataEffects
import Leanux.Proofs.WG.Config.MixedPagePlanClaims
import Leanux.Proofs.WG.Config.MixedPageScanInput
import Leanux.Proofs.WG.Config.MixedCallbackFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The serializer never increases available room, including restored-buffer
cancellation and arbitrary initial capacity. -/
theorem weightedPeerResult_room (d : Device) (nodes : NodeId → AipNode)
    (p : Peer) (ctx : DumpCtx) (skb : NlSkb) (ids : List NodeId) :
    (weightedPeerResult d nodes p ctx skb ids).1.room ≤ skb.room := by
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
        | mk front remaining => cases remaining <;> simp <;> omega
  · simp only [weightedPeerResult,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40) = cost from rfl,
      ite_eq_right fits]
    exact Nat.le_refl _

/-- Every scan spends or restores room without increasing its initial capacity. -/
theorem mixedPeerScan_room (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (rows : List MixedPeerRow) (ctx : DumpCtx)
    (cursor : Option PeerId) (skb : NlSkb) (prior : Array PeerDumpAttrs) :
    (mixedPeerScan d peers nodes rows ctx cursor skb prior).native.2.2.1.room ≤ skb.room := by
  induction rows generalizing ctx cursor skb prior with
  | nil => exact Nat.le_refl _
  | cons row rows ih =>
    obtain ⟨pid,ids⟩ := row
    have one := weightedPeerResult_room d nodes (peers pid) ctx skb ids
    cases outcome : weightedPeerResult d nodes (peers pid) ctx skb ids with
    | mk out rest =>
      obtain ⟨after,verdict⟩ := rest
      rw [outcome] at one
      cases verdict with
      | complete attrs =>
        simpa only [mixedPeerScan,outcome] using
          Nat.le_trans (ih after (some pid) out (prior.push attrs)) one
      | split attrs => simpa only [mixedPeerScan,outcome] using one
      | cancelled => simpa only [mixedPeerScan,outcome] using one

/-- The planned header-room formula is below the fresh-buffer size, even
when subtraction saturates. Native correspondence needs header capacity. -/
theorem mixedPageRoom_lt (d : Device) (ctx : DumpCtx) :
    mixedPageRoom d ctx < NLMSG_GOODSIZE := by
  simp only [mixedPageRoom,devicePrefixSpace,NLMSG_GOODSIZE]
  split <;> omega

/-- The planned scan leaves less room than the fresh-buffer size. Its positive
nonfinal return expression transfers through a separate native correspondence. -/
theorem mixedPeerScan_nonfinal_ret (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (rows : List MixedPeerRow) (ctx : DumpCtx) :
    0 < Int.ofNat (NLMSG_GOODSIZE -
      (mixedPeerScan d peers nodes rows ctx ctx.nextPeer
        {room := mixedPageRoom d ctx} #[]).native.2.2.1.room) := by
  have bounds := mixedPeerScan_room d peers nodes rows ctx ctx.nextPeer
    {room := mixedPageRoom d ctx} #[]
  have header := mixedPageRoom_lt d ctx
  dsimp only at bounds
  change (0 : Int) < ↑(NLMSG_GOODSIZE - _)
  omega

/-- A completed nonempty scan has completed a peer and reset its AIP cursor.
An empty scan retains its input, so its reset condition must hold at entry. -/
theorem mixedPeerScan_done_context (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (rows : List MixedPeerRow) (ctx : DumpCtx)
    (cursor : Option PeerId) (skb : NlSkb) (prior : Array PeerDumpAttrs)
    (empty : rows = [] → ctx.nextAllowedip = none ∧ ctx.allowedipsSeq = 0)
    (done : (mixedPeerScan d peers nodes rows ctx cursor skb prior).native.2.2.2.1 = true) :
    (mixedPeerScan d peers nodes rows ctx cursor skb prior).native.1.nextAllowedip = none ∧
      (mixedPeerScan d peers nodes rows ctx cursor skb prior).native.1.allowedipsSeq = 0 := by
  induction rows generalizing ctx cursor skb prior with
  | nil => exact empty rfl
  | cons row rows ih =>
    obtain ⟨pid,ids⟩ := row
    cases outcome : weightedPeerResult d nodes (peers pid) ctx skb ids with
    | mk out rest =>
      obtain ⟨after,verdict⟩ := rest
      cases verdict with
      | complete attrs =>
        have reset := weightedPeerResult_complete_context d nodes (peers pid) ctx skb ids attrs
          (by rw [outcome])
        rw [outcome] at reset
        change after = _ at reset
        simp only [mixedPeerScan,outcome] at done ⊢
        apply ih after (some pid) out (prior.push attrs) _ done
        intro _
        rw [reset]
        exact ⟨rfl,rfl⟩
      | split attrs => simp [mixedPeerScan,outcome] at done
      | cancelled => simp [mixedPeerScan,outcome] at done

/-- Every planned page's room is bounded by its preserved input header choice. -/
theorem mixedPages_room (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (ready : MixedPageReady d peers nodes rows ctx) :
    ∀ page ∈ mixedPages d peers nodes rows ctx ready,
      page.native.2.2.1.room ≤ mixedPageRoom d page.native.1 := by
  let result := mixedPeerScan d peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[]
  have one := mixedPeerScan_room d peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[]
  change result.native.2.2.1.room ≤ mixedPageRoom d ctx at one
  have old := mixedPeerScan_oldCursor d peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[]
  change result.native.1.nextPeer = ctx.nextPeer at old
  have resultBound : result.native.2.2.1.room ≤ mixedPageRoom d result.native.1 := by
    simpa only [mixedPageRoom,old] using one
  intro page member
  rw [mixedPages] at member
  dsimp only at member
  by_cases finished : result.remaining = []
  · rw [dite_eq_left finished] at member
    simp only [List.mem_singleton] at member
    subst page
    exact resultBound
  · rw [dite_eq_right finished] at member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact resultBound
    · exact mixedPages_room d peers nodes result.remaining
        {result.native.1 with nextPeer := result.native.2.1}
        (mixedPageReady_next d peers nodes rows ctx ready finished) page member
termination_by mixedPageMeasure rows ctx
decreasing_by exact mixedPageReady_progress d peers nodes rows ctx ready finished

/-- The final planned scan resets its AIP cursor and sequence. No reset is
invented for an initial empty scan with an arbitrary pre-existing cursor. -/
theorem mixedPages_final_context (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (ready : MixedPageReady d peers nodes rows ctx)
    (empty : rows = [] → ctx.nextAllowedip = none ∧ ctx.allowedipsSeq = 0) :
    ∃ front last, mixedPages d peers nodes rows ctx ready = front ++ [last] ∧
      last.native.1.nextAllowedip = none ∧ last.native.1.allowedipsSeq = 0 := by
  let result := mixedPeerScan d peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[]
  rw [mixedPages]
  dsimp only
  by_cases finished : result.remaining = []
  · rw [dite_eq_left finished]
    have done := (mixedPeerScan_done d peers nodes rows ctx ctx.nextPeer
      {room := mixedPageRoom d ctx} #[]).mpr finished
    exact ⟨[],result,rfl,mixedPeerScan_done_context d peers nodes rows ctx ctx.nextPeer
      {room := mixedPageRoom d ctx} #[] empty done⟩
  · rw [dite_eq_right finished]
    obtain ⟨front,last,eq,reset⟩ := mixedPages_final_context d peers nodes result.remaining
      {result.native.1 with nextPeer := result.native.2.1}
      (mixedPageReady_next d peers nodes rows ctx ready finished) (fun eq => False.elim (finished eq))
    exact ⟨result::front,last,by rw [List.cons_append,←eq],reset⟩
termination_by mixedPageMeasure rows ctx
decreasing_by exact mixedPageReady_progress d peers nodes rows ctx ready finished

/-- The pure empty-input plan still has one completed page; actual empty Device
handling supplies its separate guard/parts-none callback correspondence. -/
theorem mixedPages_empty (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (ctx : DumpCtx) (ready : MixedPageReady d peers nodes [] ctx) :
    mixedPages d peers nodes [] ctx ready =
      [⟨(ctx,ctx.nextPeer,{room := mixedPageRoom d ctx},true,#[]),[]⟩] := by
  rw [mixedPages]
  rfl

/-- Exact DATA count plus final DONE spill, with no empty-plan fallback. -/
theorem mixedPageReceiveCount_append (front : List MixedPeerScan) (last : MixedPeerScan) :
    mixedPageReceiveCount (front ++ [last]) = front.length + 1 +
      if last.native.2.2.1.room < nlmsgTotal 4 then 1 else 0 := by
  simp [mixedPageReceiveCount]

/-- One planned nonfinal DATA consumes one unit of the static receive budget. -/
theorem mixedPageReceiveCount_cons (page : MixedPeerScan) (pages : List MixedPeerScan)
    (nonempty : pages ≠ []) :
    mixedPageReceiveCount (page :: pages) = 1 + mixedPageReceiveCount pages := by
  cases pages with
  | nil => exact False.elim (nonempty rfl)
  | cons next rest =>
    cases lastEq : (next::rest).getLast? with
    | none => simp at lastEq
    | some last =>
      simp [mixedPageReceiveCount,List.getLast?_cons_cons,lastEq]
      omega

/-- Canonical plans have at least one DATA page and at most one extra DONE
receive beyond their finite page count. -/
theorem mixedPages_receive_bound (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (ready : MixedPageReady d peers nodes rows ctx) :
    let pages := mixedPages d peers nodes rows ctx ready
    pages ≠ [] ∧ pages.length ≤ mixedPageReceiveCount pages ∧
      mixedPageReceiveCount pages ≤ mixedPageMeasure rows ctx + 2 := by
  obtain ⟨front,last,eq,_,_,_,bound⟩ := mixedPages_complete d peers nodes rows ctx ready
  rw [eq] at bound ⊢
  dsimp only
  rw [mixedPageReceiveCount_append]
  simp only [List.length_append,List.length_singleton] at bound ⊢
  refine ⟨by simp,?_,?_⟩ <;> split <;> omega

/-- Appending DATA to the scan's unchanged empty skb produces exactly its
planned raw message; this is independent of the later DONE room branch. -/
theorem mixedPageCall_message (d : Device) (page : MixedPeerScan)
    (empty : page.native.2.2.1.messages = []) :
    (mixedPageCall d page).skb.messages = [mixedPageMessage d page] := by
  simp [mixedPageCall,cursorCallResult,mixedPageMessage,empty]
  split <;> rfl

end Leanux.Proofs.WG.Config
