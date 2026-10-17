import Leanux.Proofs.WG.Config.MixedPageSelectionModel
import Leanux.Proofs.WG.Config.MixedPagePlanClaims
import Leanux.Proofs.WG.Config.MixedPageScanInput
import Leanux.Proofs.WG.Config.CursorCallbackModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The exact split preserves a node occurrence suffix and identifies its head. -/
theorem weightedPeerResult_split_suffix (d : Device) (nodes : NodeId → AipNode) (p : Peer)
    (ctx : DumpCtx) (skb : NlSkb) (ids : List NodeId) (out : NlSkb) (after : DumpCtx)
    (attrs : PeerDumpAttrs)
    (splitResult : weightedPeerResult d nodes p ctx skb ids = (out,after,.split attrs)) :
    ∃ front start rest, ids = front ++ start::rest ∧
      mixedPeerRemaining nodes p ctx skb ids = start::rest ∧ after.nextAllowedip = some start := by
  let cost := if ctx.nextAllowedip.isNone then peerFixedSpace p else 40
  by_cases fitsPrefix : cost ≤ skb.room
  · simp only [weightedPeerResult,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40) = cost from rfl,
      ite_eq_left fitsPrefix] at splitResult
    cases ids with
    | nil => simp [weightedAllowedResult] at splitResult
    | cons first ids =>
      by_cases nest : skb.room-cost < 4
      · simp [weightedAllowedResult,nest] at splitResult
      · simp only [weightedAllowedResult,ite_eq_right nest] at splitResult
        cases plan : weightedPrefix nodes (skb.room-cost-4) (first::ids) with
        | mk front remaining =>
          rw [plan] at splitResult
          cases remaining with
          | nil => simp at splitResult
          | cons start rest =>
            have decomp := (weightedPrefix_spec nodes (skb.room-cost-4) (first::ids)).1
            rw [plan] at decomp
            simp only [Prod.mk.injEq] at splitResult
            refine ⟨front,start,rest,decomp.symm,?_,?_⟩
            · simp only [mixedPeerRemaining,
                show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40) = cost from rfl,plan]
            · exact congrArg DumpCtx.nextAllowedip splitResult.2.1.symm
  · simp only [weightedPeerResult,show (if ctx.nextAllowedip.isNone then peerFixedSpace p else 40) = cost from rfl,
      ite_eq_right fitsPrefix] at splitResult
    simp at splitResult

/-- Every scan retains genuine original peer/node occurrence suffixes, even
when it stops at cancellation or a zero-node split. -/
theorem mixedPeerScan_origin (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (cursor : Option PeerId)
    (skb : NlSkb) (prior : Array PeerDumpAttrs)
    (position : MixedPeerPosition d rows cursor) (suffix : MixedRowsSuffix peers rows ctx) :
    let result := mixedPeerScan d peers nodes rows ctx cursor skb prior
    MixedPeerPosition d result.remaining result.native.2.1 ∧
      MixedRowsSuffix peers result.remaining result.native.1 := by
  induction rows generalizing ctx cursor skb prior with
  | nil => exact ⟨position,trivial⟩
  | cons row rows ih =>
    obtain ⟨pid,ids⟩ := row
    have one := mixedPeerResult_progress d nodes (peers pid) ctx skb ids
    cases outcome : weightedPeerResult d nodes (peers pid) ctx skb ids with
    | mk out rest =>
      obtain ⟨after,verdict⟩ := rest
      rw [outcome] at one
      cases verdict with
      | complete attrs =>
        have reset := weightedPeerResult_complete_context d nodes (peers pid) ctx skb ids attrs
          (by rw [outcome])
        simp only [outcome] at reset
        have nextPosition : MixedPeerPosition d rows (some pid) := by
          cases cursor with
          | none => exact ⟨[],position⟩
          | some old =>
            obtain ⟨before,eq⟩ := position
            exact ⟨before++[old],by simpa only [List.map_cons,List.singleton_append,List.append_assoc] using eq⟩
        have nextSuffix : MixedRowsSuffix peers rows after := by
          cases rows with
          | nil => trivial
          | cons next tail =>
            refine ⟨?_,?_⟩
            · simpa only [reset] using suffix.2 next (by simp)
            · intro row member
              exact suffix.2 row (by simp [member])
        simpa only [mixedPeerScan,outcome] using ih after (some pid) out (prior.push attrs) nextPosition nextSuffix
      | split attrs =>
        obtain ⟨front,start,tail,split,remaining,next⟩ :=
          weightedPeerResult_split_suffix d nodes (peers pid) ctx skb ids out after attrs outcome
        simp only [mixedPeerScan,outcome,remaining]
        refine ⟨position,?_,suffix.2⟩
        simp only [next,List.head?_cons,true_and]
        have original : ∃ before, (peers pid).allowedipsList = before ++ ids := by
          cases cur : ctx.nextAllowedip with
          | none => exact ⟨[],by simpa only [MixedRowsSuffix,cur,List.nil_append] using suffix.1⟩
          | some value =>
            have picked := suffix.1
            rw [cur] at picked
            exact picked.2
        obtain ⟨before,eq⟩ := original
        exact ⟨before++front,by rw [eq,split,List.append_assoc]⟩
      | cancelled =>
        dsimp only at one
        simpa only [mixedPeerScan,outcome,MixedRowsSuffix,one.1] using And.intro position suffix

private theorem mixed_dropWhile_boundary (before tail : List Nat) (cursor : Nat)
    (fresh : cursor ∉ before) :
    (before ++ cursor::tail).dropWhile (· != cursor) = cursor::tail := by
  induction before with
  | nil => simp
  | cons id before ih =>
    have ne : id ≠ cursor := by intro eq; subst id; simp at fresh
    have rest : cursor ∉ before := by simp_all
    simp [ne,ih rest]

/-- First-match selection follows from occurrence structure and freshness only
at the computed peer/node boundaries; duplicate IDs elsewhere are unrestricted. -/
theorem mixedBoundary_selected (d : Device) (peers : PeerId → Peer)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (cursor : Option PeerId)
    (position : MixedPeerPosition d rows cursor) (suffix : MixedRowsSuffix peers rows ctx)
    (fresh : MixedBoundaryFresh d peers rows ctx cursor) :
    cursorSelected d {ctx with nextPeer := cursor} = rows.map Prod.fst ∧
      MixedRowsSelected peers rows ctx := by
  constructor
  · cases cursor with
    | none => exact position
    | some old =>
      obtain ⟨before,members⟩ := position
      have size : (before ++ old :: rows.map Prod.fst).length-rows.length-1 = before.length := by
        simp only [List.length_append,List.length_cons,List.length_map]
        omega
      have boundary := fresh.1 old rfl
      rw [members,size] at boundary
      have clean : old ∉ before := by simpa using boundary
      change (d.peerList.dropWhile (· != old)).drop 1 = rows.map Prod.fst
      rw [members,mixed_dropWhile_boundary before (rows.map Prod.fst) old clean]
      rfl
  · cases rows with
    | nil => trivial
    | cons row rows =>
      obtain ⟨pid,ids⟩ := row
      refine ⟨?_,suffix.2⟩
      cases cur : ctx.nextAllowedip with
      | none => simpa only [cur] using suffix.1
      | some start =>
        have first := suffix.1
        rw [cur] at first
        obtain ⟨head,before,members⟩ := first
        refine ⟨head,?_⟩
        have boundary := fresh.2 pid ids rows start rfl cur
        have size : (before++ids).length-ids.length = before.length := by simp
        rw [members,size] at boundary
        have clean : start ∉ before := by simpa using boundary
        cases ids with
        | nil => simp at head
        | cons first rest =>
          cases head
          rw [members]
          exact mixed_dropWhile_boundary before rest start clean

/-- The full initial occurrence rows establish structure without a uniqueness
or callback-execution premise. -/
theorem mixedInitialRows_origin (d : Device) (peers : PeerId → Peer) (ctx : DumpCtx)
    (fresh : ctx.nextAllowedip = none) :
    MixedPeerPosition d (mixedInitialRows d peers) none ∧
      MixedRowsSuffix peers (mixedInitialRows d peers) ctx := by
  constructor
  · simp [MixedPeerPosition,mixedInitialRows,List.map_map,Function.comp_def]
  · have full : ∀ row ∈ mixedInitialRows d peers, (peers row.1).allowedipsList = row.2 := by
      intro row member
      obtain ⟨pid,_,rfl⟩ := List.mem_map.mp member
      rfl
    cases rows : mixedInitialRows d peers with
    | nil => trivial
    | cons row rest =>
      refine ⟨?_,?_⟩
      · simpa only [fresh] using full row (by simp [rows])
      · intro entry member
        exact full entry (by simp [rows,member])

/-- Structural suffix provenance transports the original resident/readable
membership domain to every remaining peer and node occurrence. -/
theorem mixedOrigin_members (d : Device) (peers : PeerId → Peer)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (cursor : Option PeerId)
    (position : MixedPeerPosition d rows cursor) (suffix : MixedRowsSuffix peers rows ctx) :
    ∀ row ∈ rows, row.1 ∈ d.peerList ∧ ∀ id ∈ row.2, id ∈ (peers row.1).allowedipsList := by
  have peerMember : ∀ pid ∈ rows.map Prod.fst, pid ∈ d.peerList := by
    cases cursor with
    | none => intro pid member; rw [position]; exact member
    | some old =>
      obtain ⟨before,members⟩ := position
      intro pid member
      rw [members]
      simp [member]
  intro row member
  refine ⟨peerMember row.1 (List.mem_map_of_mem member),?_⟩
  cases rows with
  | nil => simp at member
  | cons first rows =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · intro id node
      cases cur : ctx.nextAllowedip with
      | none =>
        have listed := suffix.1
        rw [cur] at listed
        rw [listed]
        exact node
      | some start =>
        have selected := suffix.1
        rw [cur] at selected
        obtain ⟨before,listed⟩ := selected.2
        rw [listed]
        exact List.mem_append_right _ node
    · intro id node
      rw [suffix.2 row member]
      exact node

/-- Structural occurrence provenance propagates through every canonical page. -/
theorem mixedPages_origin (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (ready : MixedPageReady d peers nodes rows ctx)
    (position : MixedPeerPosition d rows ctx.nextPeer) (suffix : MixedRowsSuffix peers rows ctx) :
    ∀ page ∈ mixedPages d peers nodes rows ctx ready,
      MixedPeerPosition d page.remaining page.native.2.1 ∧
        MixedRowsSuffix peers page.remaining page.native.1 := by
  let result := mixedPeerScan d peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom d ctx} #[]
  have current := mixedPeerScan_origin d peers nodes rows ctx ctx.nextPeer
    {room := mixedPageRoom d ctx} #[] position suffix
  change MixedPeerPosition d result.remaining result.native.2.1 ∧
    MixedRowsSuffix peers result.remaining result.native.1 at current
  intro page member
  rw [mixedPages] at member
  dsimp only at member
  by_cases finished : result.remaining = []
  · rw [dite_eq_left finished] at member
    simp only [List.mem_singleton] at member
    subst page
    exact current
  · rw [dite_eq_right finished] at member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact current
    · apply mixedPages_origin d peers nodes result.remaining
        {result.native.1 with nextPeer := result.native.2.1}
        (mixedPageReady_next d peers nodes rows ctx ready finished)
        current.1 current.2 page member
termination_by mixedPageMeasure rows ctx
decreasing_by
  exact mixedPageReady_progress d peers nodes rows ctx ready finished

/-- Every computed nonfinal boundary selects precisely the next remaining
occurrences when its first-match boundary positions are fresh. -/
theorem mixedPages_selected (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (rows : List MixedPeerRow) (ctx : DumpCtx) (ready : MixedPageReady d peers nodes rows ctx)
    (position : MixedPeerPosition d rows ctx.nextPeer) (suffix : MixedRowsSuffix peers rows ctx)
    (fresh : MixedPlanFresh d peers (mixedPages d peers nodes rows ctx ready)) :
    ∀ page ∈ (mixedPages d peers nodes rows ctx ready).dropLast,
      cursorSelected d {page.native.1 with nextPeer := page.native.2.1} = page.remaining.map Prod.fst ∧
        MixedRowsSelected peers page.remaining {page.native.1 with nextPeer := page.native.2.1} := by
  intro page member
  have all : page ∈ mixedPages d peers nodes rows ctx ready := List.dropLast_subset _ member
  have origin := mixedPages_origin d peers nodes rows ctx ready position suffix page all
  exact mixedBoundary_selected d peers page.remaining page.native.1 page.native.2.1
    origin.1 origin.2 (fresh page member)

end Leanux.Proofs.WG.Config
