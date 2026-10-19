import Leanux.Proofs.WG.Config.MixedFirstSource
import Leanux.Proofs.WG.Config.MixedPageDrainSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The first acquisition bound follows from only the computed nonfinal
cursor data. A completed first page has no acquisition obligation. -/
theorem mixedFirst_cursor_refs (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (ready : MixedPageReady d peers nodes (mixedInitialRows d peers) {hasWg := true})
    (cursorData : MixedPlanCursorData d
      (mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready)) :
    ∀ id, (if (mixedFirstScan d peers nodes).native.2.2.2.1 then none else
      (mixedFirstScan d peers nodes).native.2.1) = some id →
      ∃ p, d.peers[id]? = some p ∧ 0 < p.refcount ∧ p.refcount+1 < 2^31 := by
  let page := mixedFirstScan d peers nodes
  have oldCursor : page.native.1.nextPeer = none := mixedPeerScan_oldCursor d peers nodes
    (mixedInitialRows d peers) {hasWg := true} none {room := mixedPageRoom d {hasWg := true}} #[]
  have doneEq := mixedPeerScan_done d peers nodes (mixedInitialRows d peers) {hasWg := true}
    none {room := mixedPageRoom d {hasWg := true}} #[]
  change page.native.2.2.2.1 = true ↔ page.remaining = [] at doneEq
  intro id chosen
  change (if page.native.2.2.2.1 then none else page.native.2.1) = some id at chosen
  cases done : page.native.2.2.2.1 with
  | true => simp [done] at chosen
  | false =>
    have unfinished : page.remaining ≠ [] := by intro eq; have h := doneEq.mpr eq; simp [done] at h
    have nextReady := mixedPageReady_next d peers nodes (mixedInitialRows d peers) {hasWg := true} ready unfinished
    let tail := mixedPages d peers nodes page.remaining {page.native.1 with nextPeer := page.native.2.1} nextReady
    have planEq : mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready = page::tail := by
      rw [mixedPages]
      exact dite_eq_right unfinished
    have nonempty : tail ≠ [] := (mixedPages_receive_bound d peers nodes page.remaining
      {page.native.1 with nextPeer := page.native.2.1} nextReady).1
    obtain ⟨first,rest,eq⟩ := List.exists_cons_of_ne_nil nonempty
    have headMember : page ∈ (mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready).dropLast := by
      rw [planEq,eq]
      simp
    have atNext : page.native.2.1 = some id := by simpa only [done,Bool.false_eq_true,ite_false] using chosen
    obtain ⟨p,found,_,positive,bound⟩ := cursorData page headMember id atNext
    exact ⟨p,found,positive,by simpa [oldCursor] using bound⟩

/-- Complete original getter drain after its actual first callback. Initial
empty Device, one-page completion, and arbitrary finite mixed tails share the
same canonical plan and exact ordered cursor-reference Device fold. -/
theorem mixedGetter_drain_source (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (sock : NlSock)
    (ready : MixedPageReady d peers nodes (mixedInitialRows d peers) {hasWg := true})
    (residents : ∀ id ∈ d.peerList, d.peers[id]? = some (peers id))
    (readable : ∀ pid ∈ d.peerList, ∀ id ∈ (peers pid).allowedipsList, d.nodes[id]? = some (nodes id))
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (fresh : MixedPlanFresh d peers (mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready))
    (cursorData : MixedPlanCursorData d (mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready))
    (emptyQueue : sock.queue = []) :
    let pages := mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready
    CursorHeld d (mixedPagesDevice d pages) none ∧
      PageDrainContract (mixedFirstDevice d peers nodes) (mixedFirstSocket d peers nodes sock)
        (mixedPagesDevice d pages) (socketReadbackFinal sock d)
        (mixedPageMessages d pages) (mixedPageReceiveCount pages) := by
  let page := mixedFirstScan d peers nodes
  let call := mixedPeersFirstCall d peers nodes
  let outAttrs := if page.native.1.nextPeer.isNone then deviceFixedAttrs d else []
  let outParts := if d.peerList.isEmpty then none else some page.native.2.2.2.2.toList
  have metadata := mixedPeerScan_metadata d peers nodes (mixedInitialRows d peers) {hasWg := true}
    none {room := mixedPageRoom d {hasWg := true}} #[] (Or.inl rfl)
  change page.native.1.hasWg = true ∧ _ at metadata
  have oldCursor : page.native.1.nextPeer = none := mixedPeerScan_oldCursor d peers nodes
    (mixedInitialRows d peers) {hasWg := true} none {room := mixedPageRoom d {hasWg := true}} #[]
  have data : call.skb.messages = [.data 2 outAttrs outParts] :=
    mixedPageCall_message d page metadata.2.2
  have initial := mixedInitialRows_origin d peers {hasWg := true} rfl
  have origin := mixedPeerScan_origin d peers nodes (mixedInitialRows d peers) {hasWg := true}
    none {room := mixedPageRoom d {hasWg := true}} #[] initial.1 initial.2
  have doneEq := mixedPeerScan_done d peers nodes (mixedInitialRows d peers) {hasWg := true}
    none {room := mixedPageRoom d {hasWg := true}} #[]
  change page.native.2.2.2.1 = true ↔ page.remaining = [] at doneEq
  by_cases finished : page.remaining = []
  · have done : page.native.2.2.2.1 = true := doneEq.mpr finished
    have planEq : mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready = [page] := by
      rw [mixedPages]
      exact dite_eq_left finished
    have firstDevice : mixedFirstDevice d peers nodes = d := by
      change cursorAcquired d (if page.native.2.2.2.1 then none else page.native.2.1) = d
      simp [done,cursorAcquired]
    have finalDevice : mixedPagesDevice d [page] = d := by
      simp [mixedPagesDevice,done,oldCursor,cursorHandoff,cursorAcquired,cursorReleased]
    have completed : call.ret = 0 := by
      change (if page.native.2.2.2.1 then 0 else Int.ofNat (NLMSG_GOODSIZE-page.native.2.2.1.room)) = 0
      simp [done]
    have reset := mixedPeerScan_done_context d peers nodes (mixedInitialRows d peers) {hasWg := true}
      none {room := mixedPageRoom d {hasWg := true}} #[] (fun _ => ⟨rfl,rfl⟩) done
    change page.native.1.nextAllowedip = none ∧ page.native.1.allowedipsSeq = 0 at reset
    have callCtx : call.ctx = {hasWg := true} := by
      change {page.native.1 with nextPeer := if page.native.2.2.2.1 then none else page.native.2.1} = _
      rw [done]
      cases hctx : page.native.1 with
      | mk old seq aip wg =>
        simp only [hctx] at reset metadata
        simp only [reset.1,reset.2,metadata.1,ite_true]
    let started : NlSock := {sock with cbRunning := true,dumpDoneErrno := INT_MAX,prevSeq := 0,ctx := {hasWg := true}}
    have drain := pageDrain_completed d started call outAttrs outParts rfl callCtx rfl data
    have count : (if call.skb.room < nlmsgTotal 4 then 2 else 1) ≤ mixedPageReceiveCount [page] := by
      have restored : page.native.2.2.1.room ≤ call.skb.room :=
        Nat.le_add_right _ _
      simp only [mixedPageReceiveCount,List.getLast?_singleton,List.length_singleton]
      by_cases actualSpill : call.skb.room < nlmsgTotal 4
      · have rawSpill : page.native.2.2.1.room < nlmsgTotal 4 := by omega
        simp [actualSpill,rawSpill]
      · simp only [actualSpill,ite_false]
        split <;> omega
    have bounded : PageDrainContract d (paginationCompletedSocket started call) d
        (socketReadbackFinal started d) [.data 2 outAttrs outParts,.done 2 0]
        (mixedPageReceiveCount [page]) := by
      intro step budget acc enough
      exact drain step budget acc (Nat.le_trans count enough)
    refine ⟨?_,?_⟩
    · simp [planEq,finalDevice,CursorHeld]
    · rw [planEq,finalDevice,firstDevice]
      simpa [mixedFirstSocket,show mixedPeersFirstCall d peers nodes = call from rfl,completed,
        emptyQueue,mixedPageMessages,mixedPageMessage,outAttrs,outParts,started,socketReadbackFinal] using bounded
  · have notDone : page.native.2.2.2.1 = false := by
      cases done : page.native.2.2.2.1
      · rfl
      · exact False.elim (finished (doneEq.mp done))
    let nextCtx := {page.native.1 with nextPeer := page.native.2.1}
    have nextReady := mixedPageReady_next d peers nodes (mixedInitialRows d peers) {hasWg := true} ready finished
    let tail := mixedPages d peers nodes page.remaining nextCtx nextReady
    have planEq : mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready = page::tail := by
      rw [mixedPages]
      exact dite_eq_right finished
    have tailNonempty : tail ≠ [] := (mixedPages_receive_bound d peers nodes page.remaining nextCtx nextReady).1
    obtain ⟨first,rest,tailEq⟩ := List.exists_cons_of_ne_nil tailNonempty
    have freshParts : MixedBoundaryFresh d peers page.remaining page.native.1 page.native.2.1 ∧
        MixedPlanFresh d peers tail := by
      have h := fresh
      rw [planEq,tailEq] at h
      simp only [MixedPlanFresh,List.dropLast_cons_cons,List.mem_cons,forall_eq_or_imp] at h
      refine ⟨h.1,?_⟩
      change MixedPlanFresh d peers tail
      rw [tailEq]
      exact h.2
    have dataParts := (mixedPlanCursorData_cons d page first rest).mp (by
      simpa only [planEq,tailEq] using cursorData)
    have held : CursorHeld d (mixedFirstDevice d peers nodes) nextCtx.nextPeer := by
      have h := cursorHeld_step d d none page.native.2.1 (by simp [CursorHeld])
        (by intro id impossible; cases impossible)
        (by intro id eq; obtain ⟨p,found,_,_,_⟩ := dataParts.1 id eq; exact ⟨p,found⟩)
      simpa only [mixedFirstDevice,show mixedFirstScan d peers nodes = page from rfl,notDone,
        Bool.false_eq_true,ite_false,cursorHandoff,cursorReleased] using h
    have more : 0 < call.ret := by
      change (0 : Int) < (if page.native.2.2.2.1 then 0 else Int.ofNat (NLMSG_GOODSIZE-page.native.2.2.1.room))
      rw [notDone]
      exact mixedPeerScan_nonfinal_ret d peers nodes (mixedInitialRows d peers) {hasWg := true}
    have notZero : call.ret ≠ 0 := by omega
    have oldData : ∀ id, nextCtx.nextPeer = some id → ∃ p,
        d.peers[id]? = some p ∧ p.isDead = false ∧ 0 < p.refcount := by
      intro id eq
      obtain ⟨p,found,live,positive,_⟩ := dataParts.1 id eq
      exact ⟨p,found,live,positive⟩
    have remainingData : MixedPlanCursorData d tail := by rw [tailEq]; exact dataParts.2
    have actual := mixedPages_drain_contract d (mixedFirstDevice d peers nodes) peers nodes
      page.remaining nextCtx nextReady (mixedFirstSocket d peers nodes sock) call.skb outAttrs outParts
      finished held origin.1 origin.2 freshParts.1 residents readable metadata.2.1 metadata.1 headerFits
      oldData freshParts.2 remainingData
      (by simp [mixedFirstSocket,show mixedPeersFirstCall d peers nodes = call from rfl,notZero,emptyQueue])
      (by simp [mixedFirstSocket,show mixedPeersFirstCall d peers nodes = call from rfl,notZero])
      (by simpa [mixedFirstSocket,show mixedPeersFirstCall d peers nodes = call from rfl,notZero] using more)
      (by simp only [mixedFirstSocket,show mixedPeersFirstCall d peers nodes = call from rfl,ite_eq_right notZero]
          change {page.native.1 with nextPeer := if page.native.2.2.2.1 then none else page.native.2.1} = nextCtx
          simp only [notDone,Bool.false_eq_true,ite_false,nextCtx])
      (by simp only [mixedFirstSocket,show mixedPeersFirstCall d peers nodes = call from rfl,ite_eq_right notZero]; rfl)
      data
    have fold : mixedPagesDevice d (mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready) =
        mixedPagesDevice (mixedFirstDevice d peers nodes) tail := by
      simp only [planEq,mixedPagesDevice,notDone,Bool.false_eq_true,ite_false,oldCursor,
        mixedFirstDevice,show mixedFirstScan d peers nodes = page from rfl,cursorHandoff,cursorReleased]
    have count : mixedPageReceiveCount (mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready) =
        mixedPageReceiveCount tail+1 := by
      rw [planEq,mixedPageReceiveCount_cons page tail tailNonempty]
      omega
    dsimp only
    rw [fold,count]
    simpa only [planEq,mixedPageMessages,List.map_cons,List.cons_append,mixedPageMessage,outAttrs,outParts,
      mixedFirstSocket,show mixedPeersFirstCall d peers nodes = call from rfl,ite_eq_right notZero,socketReadbackFinal] using actual

end Leanux.Proofs.WG.Config
