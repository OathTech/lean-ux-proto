import Leanux.Proofs.WG.Config.PeerPageStartModel
import Leanux.Proofs.WG.Config.TwoPageCallbackSource
import Leanux.Proofs.WG.Config.DeviceTransitionSource
import Leanux.Proofs.WG.Config.PaginationStartSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The actual fresh header ends immediately before the four-byte peer nest. -/
theorem peerFirstHeader_exact (d : Device) (fits : devicePrefixSpace d ≤ NLMSG_GOODSIZE) :
    cursorHeaderSkb d {hasWg := true} {} =
      {room := NLMSG_GOODSIZE-(devicePrefixSpace d-4)} := by
  cases identity : d.staticIdentity.hasIdentity with
  | false =>
    simp only [devicePrefixSpace,identity,Bool.false_eq_true,ite_false,NLMSG_GOODSIZE] at fits
    have name : ¬3732 < nlaTotal (d.ifname.length+1) := by omega
    simp [cursorHeaderSkb,NlSkb.put,nlmsgTotal,identity,devicePrefixSpace,
      show nlaTotal 2 = 8 from rfl,show nlaTotal 4 = 8 from rfl,name,NLMSG_GOODSIZE]
    omega
  | true =>
    simp only [devicePrefixSpace,identity,ite_true,NLMSG_GOODSIZE] at fits
    have name : ¬3732 < nlaTotal (d.ifname.length+1) := by omega
    have priv : ¬3732-nlaTotal (d.ifname.length+1) < 36 := by omega
    have pub : ¬3696-nlaTotal (d.ifname.length+1) < 36 := by omega
    simp [cursorHeaderSkb,NlSkb.put,nlmsgTotal,identity,devicePrefixSpace,
      show nlaTotal 2 = 8 from rfl,show nlaTotal 4 = 8 from rfl,
      show nlaTotal 32 = 36 from rfl,name,priv,pub,NLMSG_GOODSIZE,Nat.sub_sub]
    omega

/-- Exact-cost completing first callback, including the mirror's empty-list
peer-nest room behavior and arbitrary final DONE room. -/
theorem peerFirst_complete_returns (d : Device) (peers : PeerId → Peer)
    (residents : ∀ pid ∈ d.peerList, d.peers[pid]? = some (peers pid))
    (empty : ∀ pid ∈ d.peerList, (peers pid).allowedipsList = [])
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (fits : multiPeerSpace peers d.peerList ≤ NLMSG_GOODSIZE-devicePrefixSpace d) :
    Returns (wgGetDeviceDump {hasWg := true} 0 {}) (fun g => g.dev = some d)
      (fun result g => result = multiPeerCall d peers d.peerList ∧ g.dev = some d) := by
  let header := cursorHeaderSkb d {hasWg := true} {}
  have exactHeader := peerFirstHeader_exact d headerFits
  have lower : 48 ≤ devicePrefixSpace d := by unfold devicePrefixSpace; omega
  have nest : 4 ≤ header.room := by dsimp [header]; rw [exactHeader]; dsimp; omega
  have room : header.room-4 = NLMSG_GOODSIZE-devicePrefixSpace d := by
    dsimp [header]; rw [exactHeader]; dsimp; omega
  have headerMessages : header.messages = [] := by dsimp [header]; rw [exactHeader]
  let R : DumpCall → WGWorld → Prop := fun result g =>
    result = multiPeerCall d peers d.peerList ∧ g.dev = some d
  have finish (skb : NlSkb) (parts : Option (Array PeerDumpAttrs)) (cursor : Option PeerId) :
      Returns (cursorDumpFinish d 2 (deviceFixedAttrs d) {hasWg := true} cursor skb true parts)
        (fun g => g.dev = some d)
        (fun result g => result = cursorCallResult d 2 (deviceFixedAttrs d)
          {hasWg := true} cursor skb true parts ∧ g.dev = some d) := by
    intro g ambient device
    simp [cursorDumpFinish,WG.andM,branch,AmbientM.branch,peerPut]
    refine ⟨_,g,⟨_,rfl⟩,?_,device⟩
    rfl
  have body : Returns (cursorDumpBody d {hasWg := true} 2 (deviceFixedAttrs d) header)
      (fun g => g.dev = some d) R := by
    cases members : d.peerList with
    | nil =>
      intro g ambient device
      have short : ¬header.room < 4 := by omega
      simp [cursorDumpBody,NlSkb.put,nlaTotal,short,cursorDumpGuard,members,
        WG.orM,branch,AmbientM.branch,cursorDumpFinish,WG.andM,peerPut]
      refine ⟨_,g,⟨_,rfl⟩,?_,device⟩
      simp [multiPeerCall,members,multiPeerSpace,room,headerMessages]
    | cons pid ids =>
      have loop : Returns (cursorLoopFinish d d.peerList {hasWg := true} 2
          (deviceFixedAttrs d) {header with room := header.room-4}) (fun g => g.dev = some d) R := by
        apply TwoPage.cursorLoopFinish_returns d peers d.peerList _ 2 _ _ residents empty rfl R
        dsimp only
        rw [TwoPage.fixedPeersRun_complete peers d.peerList {hasWg := true} rfl rfl none _ #[]
          (by simpa only [room] using fits)]
        have tail := finish {header with room := header.room-4-multiPeerSpace peers d.peerList}
          (some (multiPeerParts peers d.peerList).toArray) d.peerList.getLast?
        simpa [R,cursorCallResult,multiPeerCall,members,room,headerMessages] using tail
      apply TwoPage.cursorBody_loop_returns d {hasWg := true} 2 (deviceFixedAttrs d) header R nest
        (by intro pid h; cases h) ?_ loop
      simp [cursorGuardValue,members]
  have call := TwoPage.cursorHeader_fresh_returns d {hasWg := true} 0 (fun _ => headerFits)
    (cursorDumpBody d {hasWg := true}) (fun g => g.dev = some d) R (by simpa [header] using body)
  intro g ambient device
  obtain ⟨result,final,after,run,post⟩ := call g ambient device
  refine ⟨result,final,after,?_,post⟩
  rw [wgGetDeviceDump_cursor_factor]
  simp [getDev,device]
  exact run

/-- The actual canonical first callback. Only its computed nonfinal cursor
needs a positive bounded reference; no cursor liveness or successful run is assumed. -/
theorem peerFirst_callback_returns (d : Device) (peers : PeerId → Peer)
    (residents : ∀ pid ∈ d.peerList, d.peers[pid]? = some (peers pid))
    (empty : ∀ pid ∈ d.peerList, (peers pid).allowedipsList = [])
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (firstFits : ∀ id rest, d.peerList = id :: rest →
      peerFixedSpace (peers id) ≤ NLMSG_GOODSIZE-devicePrefixSpace d)
    (cursorRefs : ∀ cursor,
      (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).2 ≠ [] →
      (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).1.getLast? = some cursor →
      0 < (peers cursor).refcount ∧ (peers cursor).refcount+1 < 2^31) :
    Returns (wgGetDeviceDump {hasWg := true} 0 {}) (fun g => g.dev = some d)
      (fun result g => result = peerFirstCall d peers ∧ g.dev = some (peerFirstDevice d peers)) := by
  let front := (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).1
  let rest := (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).2
  have split := peerPagePrefix_spec peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList
  change front ++ rest = d.peerList ∧ multiPeerSpace peers front ≤ _ ∧ _ at split
  cases remaining : rest with
  | nil =>
    have entire : front = d.peerList := by simpa [remaining] using split.1
    have complete := peerFirst_complete_returns d peers residents empty headerFits (by simpa [entire] using split.2.1)
    have restEq : (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).2 = [] := remaining
    have frontAll : (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).1 = d.peerList := entire
    simpa [peerFirstCall,peerFirstDevice,restEq,frontAll,cursorAcquired,multiPeerCall] using complete
  | cons next tail =>
    have nonempty : front ≠ [] := by
      cases members : d.peerList with
      | nil =>
        have impossible : rest = [] := by simp [rest,members,peerPagePrefix]
        rw [impossible] at remaining
        cases remaining
      | cons id ids =>
        simpa [front,members] using (peerPagePrefix_progress peers _ id ids (firstFits id ids members)).1
    obtain ⟨before,cursor,frontEq⟩ : ∃ before cursor, front = before ++ [cursor] := by
      cases reversed : front.reverse with
      | nil =>
        have emptyFront : front = [] := by simpa using congrArg List.reverse reversed
        exact False.elim (nonempty emptyFront)
      | cons cursor backwards =>
        exact ⟨backwards.reverse,cursor,by simpa using congrArg List.reverse reversed⟩
    have members : d.peerList = (before ++ [cursor]) ++ next :: tail := by
      rw [← split.1,frontEq,remaining]
    have refs := cursorRefs cursor (by change rest ≠ []; simp [remaining])
      (by change front.getLast? = some cursor; simp [frontEq])
    have header := peerFirstHeader_exact d headerFits
    have lower : 48 ≤ devicePrefixSpace d := by unfold devicePrefixSpace; omega
    have nest : 4 ≤ (cursorHeaderSkb d {hasWg := true} {}).room := by rw [header]; dsimp; omega
    have room : (cursorHeaderSkb d {hasWg := true} {}).room-4 = NLMSG_GOODSIZE-devicePrefixSpace d := by
      rw [header]; dsimp; omega
    have maximal := split.2.2 next tail remaining
    have short : NLMSG_GOODSIZE-devicePrefixSpace d-multiPeerSpace peers front < peerFixedSpace (peers next) := by
      change NLMSG_GOODSIZE-devicePrefixSpace d < multiPeerSpace peers front + peerFixedSpace (peers next) at maximal
      omega
    have callback := TwoPage.first_callback_returns d peers before cursor next tail members residents empty
      headerFits nest (by rw [room,← frontEq]; exact split.2.1)
      (by rw [room,← frontEq]; exact short) refs.1 refs.2
    have subtraction : NLMSG_GOODSIZE-(devicePrefixSpace d-4)-4 = NLMSG_GOODSIZE-devicePrefixSpace d := by omega
    have restEq : (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).2 = next :: tail := remaining
    have frontAll : (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).1 = before ++ [cursor] := frontEq
    have listed : d.peerList.isEmpty = false := by simp [members]
    simpa [peerFirstCall,peerFirstDevice,restEq,frontAll,listed,cursorCallResult,header,subtraction] using callback

/-- Original idle start and canonical first callback, with all callback premises
discharged from the plan. Existing socket envelopes remain before the new DATA. -/
theorem peerFirst_start_returns (d : Device) (peers : PeerId → Peer) (sock : NlSock)
    (residents : ∀ pid ∈ d.peerList, d.peers[pid]? = some (peers pid))
    (empty : ∀ pid ∈ d.peerList, (peers pid).allowedipsList = [])
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (firstFits : ∀ id rest, d.peerList = id :: rest →
      peerFixedSpace (peers id) ≤ NLMSG_GOODSIZE-devicePrefixSpace d)
    (cursorRefs : ∀ cursor,
      (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).2 ≠ [] →
      (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).1.getLast? = some cursor →
      0 < (peers cursor).refcount ∧ (peers cursor).refcount+1 < 2^31)
    (idle : sock.cbRunning = false) :
    Returns (netlinkDumpStart 7 (byIndex d))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
      (fun _ g => g.dev = some (peerFirstDevice d peers) ∧
        g.nlSock7 = peerFirstSocket d peers sock) := by
  have callback := peerFirst_callback_returns d peers residents empty headerFits firstFits cursorRefs
  cases remainder : (peerPagePrefix peers (NLMSG_GOODSIZE-devicePrefixSpace d) d.peerList).2 with
  | nil =>
    have device : peerFirstDevice d peers = d := by simp [peerFirstDevice,remainder,cursorAcquired]
    have completed : (peerFirstCall d peers).ret = 0 := by simp [peerFirstCall,remainder]
    have cursor : (peerFirstCall d peers).ctx.nextPeer = none := by simp [peerFirstCall,remainder]
    have start := netlinkDumpStart_completed d sock (peerFirstCall d peers) idle completed cursor
      (by simpa only [device] using callback)
    simpa [peerFirstSocket,completed,device] using start
  | cons next rest =>
    have more : 0 < (peerFirstCall d peers).ret := by
      simp only [peerFirstCall,remainder,List.isEmpty_cons,Bool.false_eq_true,ite_false]
      apply Int.natCast_pos.mpr
      have lower : 48 ≤ devicePrefixSpace d := by unfold devicePrefixSpace; omega
      unfold NLMSG_GOODSIZE at *
      omega
    have start := netlinkDumpStart_more_device_transition d (peerFirstDevice d peers) sock
      (peerFirstCall d peers) idle more callback
    have notDone : (peerFirstCall d peers).ret ≠ 0 := by omega
    simpa [peerFirstSocket,notDone] using start

end Leanux.Proofs.WG.Config
