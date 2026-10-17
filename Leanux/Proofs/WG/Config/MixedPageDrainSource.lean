import Leanux.Proofs.WG.Config.MixedHeldCallbackSource
import Leanux.Proofs.WG.Config.MixedPageDeviceClaims
import Leanux.Proofs.WG.Config.MixedPageBoundsClaims
import Leanux.Proofs.WG.Config.MixedPageSelectionClaims
import Leanux.Proofs.WG.Config.PageDrainSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Actual finite resumed producer and drain. Every callback and reference
handoff is derived from the computed mixed plan and baseline occurrence data.
The budget is sufficient for the actual receives, not a callback-success premise. -/
theorem mixedPages_drain_contract (base current : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (rows : List MixedPeerRow) (ctx : DumpCtx)
    (ready : MixedPageReady base peers nodes rows ctx)
    (sock : NlSock) (previous : NlSkb) (attrs : List (String × Json))
    (parts : Option (List PeerDumpAttrs))
    (nonempty : rows ≠ []) (held : CursorHeld base current ctx.nextPeer)
    (position : MixedPeerPosition base rows ctx.nextPeer)
    (suffix : MixedRowsSuffix peers rows ctx)
    (fresh : MixedBoundaryFresh base peers rows ctx ctx.nextPeer)
    (residents : ∀ id ∈ base.peerList, base.peers[id]? = some (peers id))
    (readable : ∀ pid ∈ base.peerList, ∀ id ∈ (peers pid).allowedipsList,
      base.nodes[id]? = some (nodes id))
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = base.peerAllowedips.seq)
    (hasWg : ctx.hasWg = true) (header : devicePrefixSpace base ≤ NLMSG_GOODSIZE)
    (oldData : ∀ id, ctx.nextPeer = some id → ∃ p,
      base.peers[id]? = some p ∧ p.isDead = false ∧ 0 < p.refcount)
    (boundaries : MixedPlanFresh base peers (mixedPages base peers nodes rows ctx ready))
    (cursorData : MixedPlanCursorData base (mixedPages base peers nodes rows ctx ready))
    (queued : sock.queue = [previous]) (running : sock.cbRunning = true)
    (active : 0 < sock.dumpDoneErrno) (cursor : sock.ctx = ctx)
    (generation : sock.prevSeq = base.deviceUpdateGen)
    (data : previous.messages = [.data 2 attrs parts]) :
    let pages := mixedPages base peers nodes rows ctx ready
    let finalDevice := mixedPagesDevice current pages
    CursorHeld base finalDevice none ∧
      PageDrainContract current sock finalDevice (socketReadbackFinal sock base)
        (.data 2 attrs parts :: mixedPageMessages base pages)
        (mixedPageReceiveCount pages + 1) := by
  let page := mixedPeerScan base peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom base ctx} #[]
  have selected := mixedBoundary_selected base peers rows ctx ctx.nextPeer position suffix fresh
  have rowIds : rows.map Prod.fst = cursorSelected base ctx := by simpa using selected.1.symm
  have membership := mixedOrigin_members base peers rows ctx ctx.nextPeer position suffix
  have baseNonempty : base.peerList ≠ [] := by
    intro empty
    have idsEmpty : rows.map Prod.fst = [] := by
      cases old : ctx.nextPeer <;> simpa [cursorSelected,empty,old] using rowIds
    exact nonempty (List.map_eq_nil_iff.mp idsEmpty)
  have continues : cursorGuardValue base ctx = false := by
    cases old : ctx.nextPeer with
    | none => simp [cursorGuardValue,old,baseNonempty]
    | some id =>
      obtain ⟨p,found,live,_⟩ := oldData id old
      simp [cursorGuardValue,old,found,live,baseNonempty]
  have rowResidents : ∀ row ∈ rows, base.peers[row.1]? = some (peers row.1) := by
    intro row member
    exact residents row.1 (membership row member).1
  have rowReadable : ∀ row ∈ rows, ∀ id ∈ row.2, base.nodes[id]? = some (nodes id) := by
    intro row member id node
    exact readable row.1 (membership row member).1 id ((membership row member).2 id node)
  have oldRefs : ∀ id, ctx.nextPeer = some id → ∃ p,
      base.peers[id]? = some p ∧ 0 < p.refcount := by
    intro id eq
    obtain ⟨p,found,_,positive⟩ := oldData id eq
    exact ⟨p,found,positive⟩
  have metadata := mixedPeerScan_metadata base peers nodes rows ctx ctx.nextPeer
    {room := mixedPageRoom base ctx} #[] sequence
  change page.native.1.hasWg = ctx.hasWg ∧ _ at metadata
  have oldCursor := mixedPeerScan_oldCursor base peers nodes rows ctx ctx.nextPeer
    {room := mixedPageRoom base ctx} #[]
  change page.native.1.nextPeer = ctx.nextPeer at oldCursor
  have actual := mixedPage_held_returns base current peers nodes rows ctx base.deviceUpdateGen
    held rowResidents rowReadable selected.2 sequence rowIds continues (fun _ => header) oldRefs
  dsimp only at actual
  have pageEq : mixedPeerScan base peers nodes rows ctx ctx.nextPeer {room := mixedPageRoom base ctx} #[] = page := rfl
  rw [pageEq] at actual
  let call := mixedPageCall base page
  let outAttrs := if page.native.1.nextPeer.isNone then deviceFixedAttrs base else []
  let outParts := if base.peerList.isEmpty then none else some page.native.2.2.2.2.toList
  have callData : call.skb.messages = [.data 2 outAttrs outParts] :=
    mixedPageCall_message base page metadata.2.2
  have doneEq := mixedPeerScan_done base peers nodes rows ctx ctx.nextPeer
    {room := mixedPageRoom base ctx} #[]
  change page.native.2.2.2.1 = true ↔ page.remaining = [] at doneEq
  by_cases finished : page.remaining = []
  · have done : page.native.2.2.2.1 = true := doneEq.mpr finished
    have planEq : mixedPages base peers nodes rows ctx ready = [page] := by
      rw [mixedPages]
      exact dite_eq_left finished
    have readyNew : ∀ id, (if page.native.2.2.2.1 then none else page.native.2.1) = some id →
        ∃ p, base.peers[id]? = some p ∧ 0 < p.refcount ∧
          p.refcount+1+(if ctx.nextPeer = some id then 1 else 0) < 2^31 := by
      simp only [done,ite_true]
      intro id impossible
      cases impossible
    obtain ⟨nextHeld,native⟩ := actual readyNew
    let nextDevice := cursorHandoff current ctx.nextPeer none
    have nextHeld' : CursorHeld base nextDevice none := by simpa only [done,ite_true] using nextHeld
    have callback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
        (fun g => g.dev = some current)
        (fun result g => result = call ∧ g.dev = some nextDevice) := by
      simpa [cursor,generation,call,mixedPageCall,cursorCallResult,oldCursor,baseNonempty,done,nextDevice] using native
    have reset := mixedPeerScan_done_context base peers nodes rows ctx ctx.nextPeer
      {room := mixedPageRoom base ctx} #[] (fun eq => False.elim (nonempty eq)) done
    change page.native.1.nextAllowedip = none ∧ page.native.1.allowedipsSeq = 0 at reset
    have callCtx : call.ctx = {hasWg := true} := by
      change {page.native.1 with nextPeer := if page.native.2.2.2.1 then none else page.native.2.1} = _
      rw [done]
      cases hctx : page.native.1 with
      | mk peer seq aip wg =>
        simp only [hctx] at reset metadata
        simp only [reset.1,reset.2,metadata.1,hasWg,ite_true]
    have completed : call.ret = 0 := by simp [call,mixedPageCall,cursorCallResult,done]
    have receive : Returns (netlinkRecvmsg 7)
        (fun g => g.dev = some current ∧ g.nlSock7 = sock)
        (fun result g => result = some [.data 2 attrs parts] ∧ g.dev = some nextDevice ∧
          g.nlSock7 = paginationCompletedSocket sock call) := by
      simpa only [data] using netlinkRecvmsg_completing_device_transition current nextDevice sock previous call
        queued running active completed (congrArg DumpCtx.nextPeer callCtx) callback
    have genFinal : nextDevice.deviceUpdateGen = base.deviceUpdateGen := by
      have h := congrArg Device.deviceUpdateGen nextHeld'.1
      exact h
    have tail := pageDrain_completed nextDevice sock call outAttrs outParts running callCtx
      (by simpa [call,mixedPageCall,cursorCallResult] using genFinal.symm) callData
    have all := pageDrain_prepend current nextDevice nextDevice sock
      (paginationCompletedSocket sock call) (socketReadbackFinal sock nextDevice) attrs parts
      [.data 2 outAttrs outParts,.done 2 0]
      (if call.skb.room < nlmsgTotal 4 then 2 else 1) receive tail
    have count : (if call.skb.room < nlmsgTotal 4 then 2 else 1) + 1 =
        mixedPageReceiveCount [page] + 1 := by
      simp only [mixedPageReceiveCount,List.getLast?_singleton,List.length_singleton]
      change (if page.native.2.2.1.room < nlmsgTotal 4 then 2 else 1) + 1 = _
      split <;> omega
    rw [count] at all
    refine ⟨?_,?_⟩
    · simpa [planEq,mixedPagesDevice,done,oldCursor,nextDevice] using nextHeld'
    · simpa [planEq,mixedPagesDevice,done,oldCursor,nextDevice,mixedPageMessages,mixedPageMessage,
        outAttrs,outParts,socketReadbackFinal,genFinal] using all
  · have notDone : page.native.2.2.2.1 = false := by
      cases h : page.native.2.2.2.1
      · rfl
      · exact False.elim (finished (doneEq.mp h))
    let nextCtx := {page.native.1 with nextPeer := page.native.2.1}
    have nextReady := mixedPageReady_next base peers nodes rows ctx ready finished
    let tailPages := mixedPages base peers nodes page.remaining nextCtx nextReady
    have planEq : mixedPages base peers nodes rows ctx ready = page :: tailPages := by
      rw [mixedPages]
      exact dite_eq_right finished
    have tailNonempty : tailPages ≠ [] :=
      (mixedPages_receive_bound base peers nodes page.remaining nextCtx nextReady).1
    obtain ⟨first,rest,tailEq⟩ := List.exists_cons_of_ne_nil tailNonempty
    have freshParts : MixedBoundaryFresh base peers page.remaining page.native.1 page.native.2.1 ∧
        MixedPlanFresh base peers tailPages := by
      have h := boundaries
      rw [planEq,tailEq] at h
      have pair := h
      simp only [MixedPlanFresh,List.dropLast_cons_cons,List.mem_cons,forall_eq_or_imp] at pair
      refine ⟨pair.1,?_⟩
      change MixedPlanFresh base peers tailPages
      rw [tailEq]
      exact pair.2
    have dataParts := (mixedPlanCursorData_cons base page first rest).mp (by
      simpa only [planEq,tailEq] using cursorData)
    have readyNew : ∀ id, (if page.native.2.2.2.1 then none else page.native.2.1) = some id →
        ∃ p, base.peers[id]? = some p ∧ 0 < p.refcount ∧
          p.refcount+1+(if ctx.nextPeer = some id then 1 else 0) < 2^31 := by
      intro id eq
      have chosen : page.native.2.1 = some id := by simpa only [notDone,Bool.false_eq_true,ite_false] using eq
      obtain ⟨p,found,_,positive,bound⟩ := dataParts.1 id chosen
      exact ⟨p,found,positive,by simpa only [oldCursor] using bound⟩
    obtain ⟨nextHeld,native⟩ := actual readyNew
    let nextDevice := cursorHandoff current ctx.nextPeer page.native.2.1
    have nextHeld' : CursorHeld base nextDevice nextCtx.nextPeer := by
      simpa only [notDone,Bool.false_eq_true,ite_false] using nextHeld
    have callback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
        (fun g => g.dev = some current)
        (fun result g => result = call ∧ g.dev = some nextDevice) := by
      simpa [cursor,generation,call,mixedPageCall,cursorCallResult,oldCursor,baseNonempty,notDone,nextDevice] using native
    have more : 0 < call.ret := by
      simpa only [call,mixedPageCall,cursorCallResult,notDone,Bool.false_eq_true,ite_false] using
        mixedPeerScan_nonfinal_ret base peers nodes rows ctx
    let nextSock : NlSock := {sock with ctx := call.ctx,prevSeq := call.prevSeq,dumpDoneErrno := call.ret,queue := [call.skb]}
    have receive : Returns (netlinkRecvmsg 7)
        (fun g => g.dev = some current ∧ g.nlSock7 = sock)
        (fun result g => result = some [.data 2 attrs parts] ∧ g.dev = some nextDevice ∧ g.nlSock7 = nextSock) := by
      simpa only [data,nextSock] using netlinkRecvmsg_more_device_transition current nextDevice sock previous call
        queued running active more callback
    have origin := mixedPeerScan_origin base peers nodes rows ctx ctx.nextPeer
      {room := mixedPageRoom base ctx} #[] position suffix
    have nextOld : ∀ id, nextCtx.nextPeer = some id → ∃ p,
        base.peers[id]? = some p ∧ p.isDead = false ∧ 0 < p.refcount := by
      intro id eq
      obtain ⟨p,found,live,positive,_⟩ := dataParts.1 id eq
      exact ⟨p,found,live,positive⟩
    have recursive := mixedPages_drain_contract base nextDevice peers nodes page.remaining nextCtx nextReady
      nextSock call.skb outAttrs outParts finished nextHeld' origin.1 origin.2 freshParts.1
      residents readable metadata.2.1 (metadata.1.trans hasWg) header nextOld freshParts.2
      (by change MixedPlanCursorData base tailPages; rw [tailEq]; exact dataParts.2)
      rfl (by simpa only [nextSock] using running) more
      (by simp only [nextSock,call,mixedPageCall,cursorCallResult,notDone,Bool.false_eq_true,ite_false,nextCtx])
      rfl callData
    obtain ⟨finalHeld,tailDrain⟩ := recursive
    have all := pageDrain_prepend current nextDevice (mixedPagesDevice nextDevice tailPages)
      sock nextSock (socketReadbackFinal nextSock base) attrs parts
      (.data 2 outAttrs outParts :: mixedPageMessages base tailPages)
      (mixedPageReceiveCount tailPages+1) receive tailDrain
    have fold : mixedPagesDevice current (mixedPages base peers nodes rows ctx ready) =
        mixedPagesDevice nextDevice tailPages := by
      simp only [planEq,mixedPagesDevice,notDone,Bool.false_eq_true,ite_false,oldCursor]
      rfl
    have count : mixedPageReceiveCount (mixedPages base peers nodes rows ctx ready)+1 =
        (mixedPageReceiveCount tailPages+1)+1 := by
      rw [planEq,mixedPageReceiveCount_cons page tailPages tailNonempty]
      omega
    refine ⟨by simpa only [fold] using finalHeld,?_⟩
    rw [fold,count]
    simpa only [planEq,mixedPageMessages,List.map_cons,List.cons_append,mixedPageMessage,
      outAttrs,outParts,nextSock,socketReadbackFinal] using all
termination_by mixedPageMeasure rows ctx
decreasing_by exact mixedPageReady_progress base peers nodes rows ctx ready finished

end Leanux.Proofs.WG.Config
