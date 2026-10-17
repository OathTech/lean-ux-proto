import Leanux.Proofs.WG.Config.PeerPageTailModel
import Leanux.Proofs.WG.Config.MiddlePageSource
import Leanux.Proofs.WG.Config.PeerPagePlanClaims
import Leanux.Proofs.WG.Config.PageDrainSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The structural plan is the exact greedy prefix once its head actually fits. -/
theorem peerTailPages_prefix (peers : PeerId → Peer) (room : Nat) (id : PeerId) (ids : List PeerId)
    (enough : 168 ≤ room) :
    peerTailPages peers room (id::ids) =
      (peerPagePrefix peers room (id::ids)).1 ::
        peerTailPages peers room (peerPagePrefix peers room (id::ids)).2 := by
  have fits : peerFixedSpace (peers id) ≤ room := Nat.le_trans (peerFixedSpace_bound _) enough
  rw [peerTailPages,peerPagePrefix,ite_eq_left fits]


/-- Actual resumed canonical producer and drain. The queued previous DATA is
returned only after the next callback runs. Every callback, reference handoff
and receive is derived from baseline peer data and the canonical plan. -/
theorem peerTail_pages_drain (base current : Device) (peers : PeerId → Peer)
    (before ids : List PeerId) (old : PeerId) (sock : NlSock) (previous : NlSkb)
    (attrs : List (String × Json)) (parts : Option (List PeerDumpAttrs))
    (nonempty : ids ≠ []) (held : CursorHeld base current (some old))
    (members : base.peerList = before ++ old :: ids) (fresh : old ∉ before)
    (residents : ∀ id ∈ base.peerList, base.peers[id]? = some (peers id))
    (empty : ∀ id ∈ base.peerList, (peers id).allowedipsList = [])
    (live : (peers old).isDead = false) (positive : 0 < (peers old).refcount)
    (boundaries : peerPageBoundaryFresh (before ++ [old]) (peerTailPages peers (NLMSG_GOODSIZE-24) ids))
    (cursorData : PeerPageCursorData peers (peerTailPages peers (NLMSG_GOODSIZE-24) ids))
    (queued : sock.queue = [previous]) (running : sock.cbRunning = true)
    (active : 0 < sock.dumpDoneErrno)
    (cursor : sock.ctx = {hasWg := true,nextPeer := some old})
    (sequence : sock.prevSeq = base.deviceUpdateGen)
    (data : previous.messages = [.data 2 attrs parts]) :
    let pages := peerTailPages peers (NLMSG_GOODSIZE-24) ids
    let finalDevice := peerPagesDevice current (some old) pages
    CursorHeld base finalDevice none ∧
      PageDrainContract current sock finalDevice (socketReadbackFinal sock base)
        (.data 2 attrs parts :: (pages.map (fun page => .data 2 [] (some (multiPeerParts peers page))) ++ [.done 2 0]))
        (peerTailReceiveCount peers pages + 1) := by
  cases idsEq : ids with
  | nil => exact False.elim (nonempty idsEq)
  | cons first ids =>
    rw [idsEq] at members boundaries cursorData
    have firstFits : peerFixedSpace (peers first) ≤ NLMSG_GOODSIZE-24 :=
      Nat.le_trans (peerFixedSpace_bound _) (by decide)
    have progress := peerPagePrefix_progress peers (NLMSG_GOODSIZE-24) first ids firstFits
    have facts := peerPagePrefix_spec peers (NLMSG_GOODSIZE-24) (first::ids)
    cases plan : peerPagePrefix peers (NLMSG_GOODSIZE-24) (first::ids) with
    | mk page remaining =>
      rw [plan] at facts progress
      dsimp only at facts progress
      have pages : peerTailPages peers (NLMSG_GOODSIZE-24) (first::ids) =
          page :: peerTailPages peers (NLMSG_GOODSIZE-24) remaining := by
        rw [peerTailPages_prefix peers (NLMSG_GOODSIZE-24) first ids (by decide),plan]
      have oldResident : base.peers[old]? = some (peers old) := residents old (by simp [members])
      cases remaining with
      | nil =>
        have pageEq : page = first::ids := by simpa using facts.1
        have pagesEq : peerTailPages peers (NLMSG_GOODSIZE-24) (first::ids) = [first::ids] := by
          simpa [peerTailPages,pageEq] using pages
        let finalDevice := cursorHandoff current (some old) none
        have finalHeld : CursorHeld base finalDevice none := cursorHeld_handoff base current old none
          (peers old) held oldResident positive (by intro id impossible; cases impossible)
        have generation : finalDevice.deviceUpdateGen = base.deviceUpdateGen := by
          have h := congrArg Device.deviceUpdateGen finalHeld.1; exact h
        let call : DumpCall := {ret := 0,ctx := {hasWg := true},prevSeq := base.deviceUpdateGen, skb := {room := NLMSG_GOODSIZE-24-multiPeerSpace peers (first::ids), messages := [.data 2 [] (some (multiPeerParts peers (first::ids)))]}}
        have callback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
            (fun g => g.dev = some current)
            (fun result g => result = call ∧ g.dev = some finalDevice) := by
          simpa [cursor,sequence,call,finalDevice] using
            cursorPage_final_returns base current peers before (first::ids) old held members fresh
              residents empty live positive (by simpa [pageEq] using facts.2.1)
        have receive : Returns (netlinkRecvmsg 7)
            (fun g => g.dev = some current ∧ g.nlSock7 = sock)
            (fun result g => result = some [.data 2 attrs parts] ∧ g.dev = some finalDevice ∧
              g.nlSock7 = paginationCompletedSocket sock call) := by
          simpa [data] using netlinkRecvmsg_completing_device_transition current finalDevice sock previous call
            queued running active rfl rfl callback
        have finalDrain := pageDrain_completed finalDevice sock call [] (some (multiPeerParts peers (first::ids)))
          running rfl (by simpa [call] using generation.symm) rfl
        have all := pageDrain_prepend current finalDevice finalDevice sock
          (paginationCompletedSocket sock call) (socketReadbackFinal sock finalDevice) attrs parts
          [.data 2 [] (some (multiPeerParts peers (first::ids))),.done 2 0]
          (if call.skb.room < nlmsgTotal 4 then 2 else 1) receive finalDrain
        refine ⟨?_,?_⟩
        · simpa [pagesEq,peerPagesDevice] using finalHeld
        · have count : (if call.skb.room < nlmsgTotal 4 then 2 else 1)+1 =
              peerTailReceiveCount peers [first::ids]+1 := by
            by_cases spill : NLMSG_GOODSIZE-24-multiPeerSpace peers (first::ids) < nlmsgTotal 4
            · simp [peerTailReceiveCount,call,spill]
            · simp [peerTailReceiveCount,call,spill]
          rw [count] at all
          simpa [pagesEq,peerPagesDevice,finalDevice,socketReadbackFinal,generation] using all
      | cons bad tail =>
        have pageEq : page = page.dropLast ++ [page.getLast progress.1] := (List.dropLast_concat_getLast progress.1).symm
        let front := page.dropLast
        let next := page.getLast progress.1
        have shape : page = front ++ [next] := pageEq
        have nextLast : page.getLast? = some next := List.getLast?_eq_some_getLast progress.1
        have restNonempty : peerTailPages peers (NLMSG_GOODSIZE-24) (bad::tail) ≠ [] := by rw [peerTailPages]; simp
        obtain ⟨restFirst,restTail,restPages⟩ := List.exists_cons_of_ne_nil restNonempty
        have boundary : next ∉ (before ++ [old]) ++ front ∧
            peerPageBoundaryFresh ((before ++ [old]) ++ (front ++ [next]))
              (peerTailPages peers (NLMSG_GOODSIZE-24) (bad::tail)) := by
          have h := boundaries
          rw [pages,restPages,pageEq] at h
          simpa [front,next,restPages] using (peerPageBoundaryFresh_cons (before ++ [old]) front next restFirst restTail).mp h
        have refs : (peers next).isDead = false ∧ 0 < (peers next).refcount ∧ (peers next).refcount+1 < 2^31 := by
          have h := cursorData
          rw [pages,restPages] at h
          exact h.1 next nextLast
        have remainingData : PeerPageCursorData peers (peerTailPages peers (NLMSG_GOODSIZE-24) (bad::tail)) := by
          have h := cursorData
          rw [pages,restPages] at h
          simpa [restPages] using h.2
        have different : next ≠ old := by
          intro same
          exact boundary.1 (by simp [same])
        have fullMembers : base.peerList = before ++ old :: ((front ++ [next]) ++ bad :: tail) := by
          rw [members,← facts.1,pageEq]
        have nextResident : base.peers[next]? = some (peers next) := residents next (by simp [fullMembers])
        let nextDevice := cursorHandoff current (some old) (some next)
        have nextHeld : CursorHeld base nextDevice (some next) := cursorHeld_handoff base current old (some next)
          (peers old) held oldResident positive
          (by intro id equal; cases equal; exact ⟨different,peers next,nextResident⟩)
        let call : DumpCall := cursorCallResult base 2 [] {hasWg := true,nextPeer := some old} (some next)
          {room := NLMSG_GOODSIZE-24-multiPeerSpace peers (front ++ [next])}
          false (some (multiPeerParts peers (front ++ [next])).toArray)
        have pageFits : multiPeerSpace peers (front ++ [next]) ≤ NLMSG_GOODSIZE-24 := by
          rw [← shape]; exact facts.2.1
        have pageShort : NLMSG_GOODSIZE-24-multiPeerSpace peers (front ++ [next]) < peerFixedSpace (peers bad) := by
          have h := facts.2.2 bad tail rfl
          rw [shape] at h
          omega
        have callback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
            (fun g => g.dev = some current)
            (fun result g => result = call ∧ g.dev = some nextDevice) := by
          simpa [cursor,sequence,call,nextDevice] using
            cursorPage_nonfinal_returns base current peers before front old next bad tail held fullMembers fresh different
              residents empty live positive refs.2.1 refs.2.2
              pageFits pageShort
        have more : 0 < call.ret := by
          change (0 : Int) < Int.ofNat (NLMSG_GOODSIZE-(NLMSG_GOODSIZE-24-multiPeerSpace peers (front ++ [next])))
          apply Int.natCast_pos.mpr
          unfold NLMSG_GOODSIZE
          omega
        let nextSock : NlSock := {sock with ctx := call.ctx,prevSeq := call.prevSeq,dumpDoneErrno := call.ret,queue := [call.skb]}
        have receive : Returns (netlinkRecvmsg 7)
            (fun g => g.dev = some current ∧ g.nlSock7 = sock)
            (fun result g => result = some [.data 2 attrs parts] ∧ g.dev = some nextDevice ∧ g.nlSock7 = nextSock) := by
          simpa [data,nextSock] using netlinkRecvmsg_more_device_transition current nextDevice sock previous call
            queued running active more callback
        have nextMembers : base.peerList = ((before ++ [old]) ++ front) ++ next :: bad :: tail := by
          simpa [List.append_assoc] using fullMembers
        have nextBoundary : peerPageBoundaryFresh (((before ++ [old]) ++ front) ++ [next])
            (peerTailPages peers (NLMSG_GOODSIZE-24) (bad::tail)) := by
          simpa [List.append_assoc] using boundary.2
        have recursive := peerTail_pages_drain base nextDevice peers ((before ++ [old]) ++ front)
          (bad::tail) next nextSock call.skb [] (some (multiPeerParts peers (front ++ [next])))
          (by simp) nextHeld nextMembers boundary.1 residents empty refs.1 refs.2.1 nextBoundary remainingData
          rfl (by simpa [nextSock] using running) more rfl rfl (by simp [call,cursorCallResult])
        obtain ⟨finalHeld,tailDrain⟩ := recursive
        have all := pageDrain_prepend current nextDevice
          (peerPagesDevice nextDevice (some next) (peerTailPages peers (NLMSG_GOODSIZE-24) (bad::tail)))
          sock nextSock (socketReadbackFinal nextSock base) attrs parts
          (.data 2 [] (some (multiPeerParts peers (front ++ [next]))) ::
            ((peerTailPages peers (NLMSG_GOODSIZE-24) (bad::tail)).map
              (fun part => .data 2 [] (some (multiPeerParts peers part))) ++ [.done 2 0]))
          (peerTailReceiveCount peers (peerTailPages peers (NLMSG_GOODSIZE-24) (bad::tail))+1)
          receive tailDrain
        have fold : peerPagesDevice current (some old) (peerTailPages peers (NLMSG_GOODSIZE-24) (first::ids)) =
            peerPagesDevice nextDevice (some next) (peerTailPages peers (NLMSG_GOODSIZE-24) (bad::tail)) := by
          simp [pages,restPages,peerPagesDevice,nextLast,nextDevice]
        have count : peerTailReceiveCount peers (peerTailPages peers (NLMSG_GOODSIZE-24) (first::ids))+1 =
            (peerTailReceiveCount peers (peerTailPages peers (NLMSG_GOODSIZE-24) (bad::tail))+1)+1 := by
          simp only [pages,restPages,peerTailReceiveCount,List.length_cons,List.getLastD,List.getLast_cons_cons]
          omega
        refine ⟨by simpa [fold] using finalHeld,?_⟩
        rw [fold,count]
        rw [pages]
        simp only [List.map_cons]
        rw [shape]
        simpa only [nextSock,socketReadbackFinal,List.cons_append] using all
termination_by ids.length
decreasing_by
  simpa only [idsEq,List.length_cons] using progress.2

end Leanux.Proofs.WG.Config
