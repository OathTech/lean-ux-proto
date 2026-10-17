import Leanux.Proofs.WG.Config.PeerPageTailSource
import Leanux.Proofs.WG.Config.PeerPageStartSource
import Leanux.Proofs.WG.Config.PeerGetterPlanClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Derive every remaining callback and receive from the canonical peer plan.
The resulting Device retains the actual ordered handoff writes. -/
theorem peerGetter_drain_source (d : Device) (peers : PeerId → Peer) (sock : NlSock)
    (residents : ∀ id ∈ d.peerList, d.peers[id]? = some (peers id))
    (empty : ∀ id ∈ d.peerList, (peers id).allowedipsList = [])
    (firstFits : ∀ id rest, d.peerList = id :: rest →
      peerFixedSpace (peers id) ≤ NLMSG_GOODSIZE-devicePrefixSpace d)
    (fresh : peerPageBoundaryFresh [] (peerPages peers d d.peerList))
    (cursorData : PeerPageCursorData peers (peerPages peers d d.peerList))
    (emptyQueue : sock.queue = []) :
    CursorHeld d (peerGetterFinalDevice d peers) none ∧
      PageDrainContract (peerFirstDevice d peers) (peerFirstSocket d peers sock)
        (peerGetterFinalDevice d peers) (socketReadbackFinal sock d)
        (peerGetterMessages d peers) (peerPageReceiveCount peers d d.peerList) := by
  have spec := peerPagePrefix_spec peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList
  cases plan : peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList with
  | mk front rest =>
    rw [plan] at spec
    dsimp only at spec
    cases rest with
    | nil =>
      have complete : (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).2 = [] := by rw [plan]
      have completed : (peerFirstCall d peers).ret = 0 := by simp [peerFirstCall,plan]
      let started : NlSock := {sock with cbRunning := true,dumpDoneErrno := INT_MAX,prevSeq := 0,ctx := {hasWg := true}}
      have drain := pageDrain_completed d started (peerFirstCall d peers)
        (deviceFixedAttrs d) (if d.peerList.isEmpty then none else some (multiPeerParts peers front))
        rfl (by simp [peerFirstCall,plan]) rfl (by simp [peerFirstCall,plan])
      refine ⟨?_,?_⟩
      · simp [peerGetterFinalDevice,plan,CursorHeld]
      · rw [peerPageReceiveCount_first_complete d peers complete]
        simpa [peerGetterFinalDevice,peerFirstDevice,peerFirstSocket,peerGetterMessages,
          plan,cursorAcquired,completed,emptyQueue,peerTailPages,socketReadbackFinal,started] using drain
    | cons next tail =>
      have remainder : (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).2 ≠ [] := by rw [plan]; simp
      have frontNonempty : front ≠ [] := by
        cases members : d.peerList with
        | nil => simp [members,peerPagePrefix] at plan
        | cons id ids =>
          have progress := peerPagePrefix_progress peers (NLMSG_GOODSIZE-devicePrefixSpace d)
            id ids (firstFits id ids members)
          have plan' : peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) (id::ids) = (front,next::tail) := by simpa [members] using plan
          rw [plan'] at progress
          exact progress.1
      obtain ⟨before,old,frontEq⟩ : ∃ before old, front = before ++ [old] := by
        cases reversed : front.reverse with
        | nil =>
          have impossible : front = [] := by simpa using congrArg List.reverse reversed
          exact False.elim (frontNonempty impossible)
        | cons old backwards =>
          exact ⟨backwards.reverse,old,by simpa using congrArg List.reverse reversed⟩
      let pages := peerTailPages peers (NLMSG_GOODSIZE-24) (next::tail)
      have pagesNonempty : pages ≠ [] := by simp [pages,peerTailPages]
      obtain ⟨page,morePages,pagesEq⟩ := List.exists_cons_of_ne_nil pagesNonempty
      have allFresh := fresh
      simp only [peerPages,plan] at allFresh
      change peerPageBoundaryFresh [] (front :: pages) at allFresh
      rw [pagesEq,frontEq,peerPageBoundaryFresh_cons] at allFresh
      have boundaries : old ∉ before ∧ peerPageBoundaryFresh (before ++ [old]) pages := by
        simpa only [List.nil_append,← pagesEq] using allFresh
      have data := cursorData
      simp only [peerPages,plan] at data
      change PeerPageCursorData peers (front :: pages) at data
      rw [pagesEq] at data
      have oldData := data.1 old (by simp [frontEq])
      have restData : PeerPageCursorData peers pages := by simpa only [pagesEq] using data.2
      have members : d.peerList = before ++ old :: (next::tail) := by
        rw [← spec.1,frontEq]
        simp only [List.append_assoc,List.singleton_append]
      have resident := residents old (by simp [members])
      have held : CursorHeld d (peerFirstDevice d peers) (some old) := by
        simpa [peerFirstDevice,plan,frontEq] using cursorHeld_acquired d old (peers old) resident
      have more : 0 < (peerFirstCall d peers).ret := by
        simp only [peerFirstCall,plan,List.isEmpty_cons,Bool.false_eq_true,ite_false]
        apply Int.natCast_pos.mpr
        have lower : 48 ≤ devicePrefixSpace d := by unfold devicePrefixSpace; omega
        unfold NLMSG_GOODSIZE at *
        omega
      have notDone : (peerFirstCall d peers).ret ≠ 0 := by omega
      have listed : d.peerList.isEmpty = false := by simp [members]
      have actual := peerTail_pages_drain d (peerFirstDevice d peers) peers before (next::tail)
        old (peerFirstSocket d peers sock) (peerFirstCall d peers).skb
        (deviceFixedAttrs d) (some (multiPeerParts peers front))
        (by simp) held members boundaries.1 residents empty oldData.1 oldData.2.1
        boundaries.2 restData
        (by simp [peerFirstSocket,notDone,emptyQueue])
        (by simp [peerFirstSocket,notDone])
        (by simpa [peerFirstSocket,notDone] using more)
        (by simp only [peerFirstSocket,ite_eq_right notDone]; simp [peerFirstCall,plan,frontEq])
        (by simp only [peerFirstSocket,ite_eq_right notDone]; rfl)
        (by simp [peerFirstCall,plan,listed])
      rw [peerPageReceiveCount_first_more d peers remainder]
      simpa [peerGetterFinalDevice,peerGetterMessages,plan,frontEq,pages,
        listed,peerFirstSocket,notDone,socketReadbackFinal,List.cons_append] using actual

end Leanux.Proofs.WG.Config
