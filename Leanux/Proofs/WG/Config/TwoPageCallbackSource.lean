import Leanux.Proofs.WG.Config.TwoPageCursorFrames
import Leanux.Proofs.WG.Config.CursorCallbackClaims
import Leanux.Proofs.WG.Config.ScalarReturns
import Leanux.Proofs.WG.Config.QueuedReferenceSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config.TwoPage
open Leanux Leanux.WG Noise Lean Std.Do

/-- Actual reference acquisition; positivity and the exact source overflow bound. -/
theorem peerGet_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (positive : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2^31) :
    Returns (peerGet pid) (fun g => g.dev = some d)
      (fun _ g => g.dev = some (cursorAcquired d (some pid))) := by
  intro g ambient device
  have nonzero : p.refcount ≠ 0 := by omega
  have nowrap : ¬2147483647 ≤ p.refcount := by omega
  have complete : ∃ x final after, ((peerGet pid).run g).run ambient = .ok ((x,final),after) := by
    simp [peerGet,requireNotPending,refcountInc,branch,branchCmp,AmbientM.branch,
      AmbientM.branchCmp,getPeer,getDev,device,resident,nonzero,nowrap,setPeer,modifyDev]
    exact ⟨_,_,_,rfl⟩
  obtain ⟨x,final,after,run⟩ := complete
  refine ⟨x,final,after,run,?_⟩
  have effect := ((ensures_iff _ _ _).mpr (Config.peerGet_exact pid d p resident))
    g ambient x final after device run
  simpa [cursorAcquired,resident,withPeer] using effect.1

/-- The acquired cursor is released without final-release guards, retaining
both actual tree-map writes rather than assuming representation restoration. -/
theorem cursorPut_releasesHeld (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (positive : 0 < p.refcount) :
    Returns (peerPut (some pid)) (fun g => g.dev = some (cursorAcquired d (some pid)))
      (fun _ g => g.dev = some (cursorReleased (cursorAcquired d (some pid)) (some pid))) := by
  have retained : 1 < p.refcount+1 := by omega
  have nonzero : p.refcount ≠ 0 := by omega
  have h := (returns_iff _ _ _).mpr (peerPut_retained_returns pid
    (cursorAcquired d (some pid)) {p with refcount := p.refcount+1}
    (by simp [cursorAcquired,resident]) retained)
  simpa [cursorReleased,cursorAcquired,resident,Index.releasedPeerDevice,nonzero,withPeer] using h

/-- Nonfinal callback holds the new cursor; the first callback has no old cursor. -/
theorem cursorFinish_acquire_returns (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (positive : 0 < p.refcount)
    (bounded : p.refcount+1 < 2^31) (ctx : DumpCtx) (old : ctx.nextPeer = none)
    (flags : Nat) (attrs : List (String × Json)) (skb : NlSkb) (parts : Option (Array PeerDumpAttrs)) :
    Returns (cursorDumpFinish d flags attrs ctx (some pid) skb false parts)
      (fun g => g.dev = some d)
      (fun result g => result = cursorCallResult d flags attrs ctx (some pid) skb false parts ∧
        g.dev = some (cursorAcquired d (some pid))) := by
  intro g ambient device
  let mark (a : Ambient) (site : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision := site,outcome,netRx := a.netRxSection}}
  let before := mark (mark (mark ambient .dumpOutRetZero true) .dumpOutNotDone true) .dumpOutHasCursor true
  obtain ⟨value,final,after,run,post⟩ := peerGet_returns pid d p resident positive bounded g before device
  cases value
  let remaining := mark (mark (mark after .peerPutNull true) .dumpRetErr false) .dumpDone false
  refine ⟨cursorCallResult d flags attrs ctx (some pid) skb false parts,final,remaining,?_,rfl,post⟩
  simp [cursorDumpFinish,WG.andM,branch,AmbientM.branch]
  change (((peerGet pid).run g).run before >>= _) = _
  rw [run]
  simp [peerPut,old,branch,AmbientM.branch,cursorCallResult,remaining,mark]

/-- Completing callback drops the held cursor; its exact Device keeps both writes. -/
theorem cursorFinish_release_returns (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (positive : 0 < p.refcount)
    (ctx : DumpCtx) (old : ctx.nextPeer = some pid) (cursor : Option PeerId)
    (flags : Nat) (attrs : List (String × Json)) (skb : NlSkb) (parts : Option (Array PeerDumpAttrs)) :
    Returns (cursorDumpFinish (cursorAcquired d (some pid)) flags attrs ctx cursor skb true parts)
      (fun g => g.dev = some (cursorAcquired d (some pid)))
      (fun result g => result = cursorCallResult (cursorAcquired d (some pid)) flags attrs ctx cursor skb true parts ∧
        g.dev = some (cursorReleased (cursorAcquired d (some pid)) (some pid))) := by
  intro g ambient device
  let mark (a : Ambient) (site : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision := site,outcome,netRx := a.netRxSection}}
  let before := mark (mark ambient .dumpOutRetZero true) .dumpOutNotDone false
  obtain ⟨value,final,after,run,post⟩ := cursorPut_releasesHeld pid d p resident positive g before device
  cases value
  let remaining := mark (mark after .dumpRetErr false) .dumpDone true
  refine ⟨cursorCallResult (cursorAcquired d (some pid)) flags attrs ctx cursor skb true parts,final,remaining,?_,rfl,post⟩
  simp [cursorDumpFinish,WG.andM,branch,AmbientM.branch,old]
  change (((peerPut (some pid)).run g).run before >>= _) = _
  rw [run]
  simp [cursorCallResult,remaining,mark]

/-- Composition through the actual finite loop; only the finalizer contract
is parameterized, and the loop execution is derived from resident empty-IP inputs. -/
theorem cursorLoopFinish_returns (d : Device) (peers : PeerId → Peer) (ids : List PeerId)
    (ctx : DumpCtx) (flags : Nat) (attrs : List (String × Json)) (skb : NlSkb)
    (residents : ∀ pid ∈ ids, d.peers[pid]? = some (peers pid))
    (empty : ∀ pid ∈ ids, (peers pid).allowedipsList = [])
    (fresh : ctx.nextAllowedip = none) (R : DumpCall → WGWorld → Prop)
    (finish : let state := fixedPeersRun peers ids ctx ctx.nextPeer skb #[]
      Returns (cursorDumpFinish d flags attrs state.1 state.2.1 state.2.2.1 state.2.2.2.1
        (some state.2.2.2.2)) (fun g => g.dev = some d) R) :
    Returns (cursorLoopFinish d ids ctx flags attrs skb) (fun g => g.dev = some d) R := by
  intro g ambient device
  obtain ⟨value,middle,remaining,run,same,valueEq⟩ :=
    fixedPeersRun_native d peers ids residents empty ctx fresh ctx.nextPeer skb #[] g ambient device
  subst value
  generalize stateEq : fixedPeersRun peers ids ctx ctx.nextPeer skb #[] = state at run finish
  obtain ⟨outCtx,cursor,outSkb,done,parts⟩ := state
  cases done with
  | false =>
    obtain ⟨result,final,after,tail,post⟩ := finish middle remaining same
    refine ⟨result,final,after,?_,post⟩
    simp only [cursorLoopFinish]
    change (((forIn ids (ctx,ctx.nextPeer,skb,true,#[]) deviceDumpPeersStep).run g).run ambient >>= _) = _
    rw [run]
    exact tail
  | true =>
    let next : Ambient := {remaining with steps := remaining.steps.push {
      decision := .dumpPeerIter,outcome := false,netRx := remaining.netRxSection}}
    obtain ⟨result,final,after,tail,post⟩ := finish middle next same
    refine ⟨result,final,after,?_,post⟩
    simp only [cursorLoopFinish]
    change (((forIn ids (ctx,ctx.nextPeer,skb,true,#[]) deviceDumpPeersStep).run g).run ambient >>= _) = _
    rw [run]
    exact tail

/-- The original fresh-buffer header has a normal run whenever its real device
prefix fits; resumed headers need no device-attribute capacity. -/
theorem cursorHeader_fresh_returns (d : Device) (ctx : DumpCtx) (prev : Nat)
    (room : ctx.nextPeer.isNone = true → devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (finish : Nat → List (String × Json) → NlSkb → WG.M DumpCall)
    (P : WGWorld → Prop) (R : DumpCall → WGWorld → Prop)
    (tail : Returns (finish (2 + if prev != 0 && prev != d.deviceUpdateGen then 16 else 0)
      (if ctx.nextPeer.isNone then deviceFixedAttrs d else []) (cursorHeaderSkb d ctx {})) P R) :
    Returns (socketDumpHeaderSource d ctx prev {} finish) P R := by
  intro g ambient pre
  have complete : ∃ header after, (cursorHeaderPrefix d ctx prev {}).run ambient = .ok (header,after) := by
    cases first : ctx.nextPeer.isNone with
    | false =>
      simp [cursorHeaderPrefix,first,NlSkb.put,nlmsgTotal,branch,AmbientM.branch]
      exact ⟨_,_,_,_,rfl⟩
    | true =>
      have capacity := room first
      cases identity : d.staticIdentity.hasIdentity with
      | false =>
        simp only [devicePrefixSpace,identity,Bool.false_eq_true,ite_false,NLMSG_GOODSIZE] at capacity
        have name : ¬3732 < nlaTotal (d.ifname.length+1) := by omega
        simp [cursorHeaderPrefix,first,identity,NlSkb.put,nlmsgTotal,
          branch,AmbientM.branch,show nlaTotal 2 = 8 from rfl,
          show nlaTotal 4 = 8 from rfl,name]
        exact ⟨_,_,_,_,rfl⟩
      | true =>
        simp only [devicePrefixSpace,identity,ite_true,NLMSG_GOODSIZE] at capacity
        have name : ¬3732 < nlaTotal (d.ifname.length+1) := by omega
        have priv : ¬3732-nlaTotal (d.ifname.length+1) < 36 := by omega
        have pub : ¬3696-nlaTotal (d.ifname.length+1) < 36 := by omega
        simp [cursorHeaderPrefix,first,identity,NlSkb.put,nlmsgTotal,
          branch,AmbientM.branch,Nat.sub_sub,show nlaTotal 2 = 8 from rfl,
          show nlaTotal 4 = 8 from rfl,show nlaTotal 32 = 36 from rfl,name,priv,pub]
        exact ⟨_,_,_,_,rfl⟩
  obtain ⟨header,remaining,headerRun⟩ := complete
  have value := cursorHeaderPrefix_normal d ctx prev {} ambient header remaining trivial headerRun
  subst header
  obtain ⟨result,final,after,finishRun,post⟩ := tail g remaining pre
  refine ⟨result,final,after,?_,post⟩
  rw [cursorHeader_source]
  change (((StateT.lift (cursorHeaderPrefix d ctx prev {}) >>= fun (flags,attrs,out) =>
    finish flags attrs out).run g).run ambient) = _
  simp only [StateT.run_bind,StateT.run_lift,bind_assoc,pure_bind]
  rw [headerRun]
  exact finishRun

/-- Source composition through the real peers-nest guard. -/
theorem cursorBody_loop_returns (d : Device) (ctx : DumpCtx) (flags : Nat)
    (attrs : List (String × Json)) (skb : NlSkb) (R : DumpCall → WGWorld → Prop)
    (room : 4 ≤ skb.room)
    (oldResident : ∀ pid, ctx.nextPeer = some pid → ∃ p, d.peers[pid]? = some p)
    (continues : cursorGuardValue d ctx = false)
    (loop : Returns (cursorLoopFinish d (cursorSelected d ctx) ctx flags attrs {skb with room := skb.room-4})
      (fun g => g.dev = some d) R) :
    Returns (cursorDumpBody d ctx flags attrs skb) (fun g => g.dev = some d) R := by
  intro g ambient device
  have enough : ¬skb.room < 4 := by omega
  let before : Ambient := {ambient with steps := ambient.steps.push {
    decision := .dumpNoPeersNest,outcome := false,netRx := ambient.netRxSection}}
  obtain ⟨value,middle,remaining,guardRun,valueEq,same⟩ := cursorDumpGuard_returns d ctx oldResident g before device
  have valueFalse : value = false := valueEq.trans continues
  subst value
  obtain ⟨result,final,after,run,post⟩ := loop middle remaining same
  refine ⟨result,final,after,?_,post⟩
  simp [cursorDumpBody,NlSkb.put,nlaTotal,enough,branch,AmbientM.branch]
  change (((cursorDumpGuard d ctx).run g).run before >>= _) = _
  rw [guardRun]
  cases cursor : ctx.nextPeer <;> simpa [cursorSelected,cursor,continues] using run

/-- Actual first callback emits the maximal completed prefix and holds its
last peer; the first nonfitting peer remains for the resumed callback. -/
theorem first_callback_returns (d : Device) (peers : PeerId → Peer) (before : List PeerId)
    (cursor next : PeerId) (tail : List PeerId)
    (members : d.peerList = (before ++ [cursor]) ++ next :: tail)
    (residents : ∀ pid ∈ d.peerList, d.peers[pid]? = some (peers pid))
    (empty : ∀ pid ∈ d.peerList, (peers pid).allowedipsList = [])
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (nestFits : 4 ≤ (cursorHeaderSkb d {hasWg := true} {}).room)
    (fits : multiPeerSpace peers (before ++ [cursor]) ≤ (cursorHeaderSkb d {hasWg := true} {}).room-4)
    (short : (cursorHeaderSkb d {hasWg := true} {}).room-4-multiPeerSpace peers (before ++ [cursor]) < peerFixedSpace (peers next))
    (positive : 0 < (peers cursor).refcount) (bounded : (peers cursor).refcount+1 < 2^31) :
    let skb := {cursorHeaderSkb d {hasWg := true} {} with room :=
      (cursorHeaderSkb d {hasWg := true} {}).room-4-multiPeerSpace peers (before ++ [cursor])}
    Returns (wgGetDeviceDump {hasWg := true} 0 {}) (fun g => g.dev = some d)
      (fun result g => result = cursorCallResult d 2 (deviceFixedAttrs d) {hasWg := true}
        (some cursor) skb false (some (multiPeerParts peers (before ++ [cursor])).toArray) ∧
        g.dev = some (cursorAcquired d (some cursor))) := by
  dsimp only
  let header := cursorHeaderSkb d {hasWg := true} {}
  let skb := {header with room := header.room-4}
  let R : DumpCall → WGWorld → Prop := fun result g =>
    result = cursorCallResult d 2 (deviceFixedAttrs d) {hasWg := true}
      (some cursor) {header with room := header.room-4-multiPeerSpace peers (before ++ [cursor])}
      false (some (multiPeerParts peers (before ++ [cursor])).toArray) ∧
      g.dev = some (cursorAcquired d (some cursor))
  have resident : d.peers[cursor]? = some (peers cursor) := residents cursor (by simp [members])
  have loop : Returns (cursorLoopFinish d d.peerList {hasWg := true} 2 (deviceFixedAttrs d) skb)
      (fun g => g.dev = some d) R := by
    apply cursorLoopFinish_returns d peers d.peerList _ 2 _ skb residents empty rfl R
    dsimp only
    rw [members,fixedPeersRun_firstSplit peers before cursor next tail skb fits short]
    exact cursorFinish_acquire_returns d cursor (peers cursor) resident positive bounded
      {hasWg := true} rfl 2 (deviceFixedAttrs d) _ _
  have body : Returns (cursorDumpBody d {hasWg := true} 2 (deviceFixedAttrs d) header)
      (fun g => g.dev = some d) R := by
    apply cursorBody_loop_returns d {hasWg := true} 2 (deviceFixedAttrs d) header R nestFits
      (by intro pid h; cases h) ?_ loop
    simp [cursorGuardValue,members]
  have call := cursorHeader_fresh_returns d {hasWg := true} 0 (fun _ => headerFits)
    (cursorDumpBody d {hasWg := true}) (fun g => g.dev = some d) R (by simpa [header] using body)
  intro g ambient device
  obtain ⟨result,final,after,run,post⟩ := call g ambient device
  refine ⟨result,final,after,?_,post⟩
  rw [wgGetDeviceDump_cursor_factor]
  simp [getDev,device]
  exact run

/-- Actual resumed callback emits every fitting remaining peer and releases
the held cursor. Duplicate later visits serialize the actual held record. -/
theorem resumed_callback_returns (d : Device) (peers : PeerId → Peer)
    (before tail : List PeerId) (cursor : PeerId)
    (members : d.peerList = before ++ cursor :: tail)
    (fresh : cursor ∉ before)
    (residents : ∀ pid ∈ d.peerList, d.peers[pid]? = some (peers pid))
    (empty : ∀ pid ∈ d.peerList, (peers pid).allowedipsList = [])
    (live : (peers cursor).isDead = false)
    (positive : 0 < (peers cursor).refcount)
    (fits : multiPeerSpace peers tail ≤ NLMSG_GOODSIZE-24) :
    Returns (wgGetDeviceDump {hasWg := true,nextPeer := some cursor} d.deviceUpdateGen {})
      (fun g => g.dev = some (cursorAcquired d (some cursor)))
      (fun result g => result =
        {ret := 0,ctx := {hasWg := true},prevSeq := d.deviceUpdateGen,
         skb := {room := NLMSG_GOODSIZE-24-multiPeerSpace peers tail, messages := [.data 2 [] (some (multiPeerParts peers tail))]}} ∧
        g.dev = some (cursorReleased (cursorAcquired d (some cursor)) (some cursor))) := by
  let held := cursorAcquired d (some cursor)
  let ctx : DumpCtx := {hasWg := true,nextPeer := some cursor}
  let hp := heldPeers peers cursor
  have resident : d.peers[cursor]? = some (peers cursor) := residents cursor (by simp [members])
  have heldResident : held.peers[cursor]? = some {peers cursor with refcount := (peers cursor).refcount+1} := by
    simp [held,cursorAcquired,resident]
  have heldMembers : held.peerList = d.peerList := by simp [held,cursorAcquired,resident]
  have heldGen : held.deviceUpdateGen = d.deviceUpdateGen := by simp [held,cursorAcquired,resident]
  have selected : cursorSelected held ctx = tail := by
    apply cursorSelected_boundary held before tail cursor (heldMembers.trans members) fresh
  have tailMember (id : PeerId) (member : id ∈ tail) : id ∈ d.peerList := by simp [members,member]
  have heldResidents : ∀ id ∈ tail, held.peers[id]? = some (hp id) := by
    intro id member
    have found := residents id (tailMember id member)
    by_cases same : id = cursor
    · subst id; simpa [hp,heldPeers] using heldResident
    · simp [held,cursorAcquired,resident,Std.TreeMap.getElem?_insert,hp,heldPeers,same,Ne.symm same,found]
  have heldEmpty : ∀ id ∈ tail, (hp id).allowedipsList = [] := by
    intro id member
    have noIps := empty id (tailMember id member)
    simp only [hp,heldPeers]
    split <;> exact noIps
  have fitsHeld : multiPeerSpace hp tail ≤ NLMSG_GOODSIZE-24 := by
    rw [(heldPeers_dump peers cursor tail).1]
    exact fits
  let R : DumpCall → WGWorld → Prop := fun result g => result =
      {ret := 0,ctx := {hasWg := true},prevSeq := d.deviceUpdateGen,
       skb := {room := NLMSG_GOODSIZE-24-multiPeerSpace peers tail, messages := [.data 2 [] (some (multiPeerParts peers tail))]}} ∧
      g.dev = some (cursorReleased held (some cursor))
  have loop : Returns (cursorLoopFinish held tail ctx 2 [] {room := NLMSG_GOODSIZE-24})
      (fun g => g.dev = some held) R := by
    apply cursorLoopFinish_returns held hp tail ctx 2 [] _ heldResidents heldEmpty rfl R
    dsimp only
    rw [fixedPeersRun_complete hp tail ctx rfl rfl (some cursor) _ #[] fitsHeld]
    have finish := cursorFinish_release_returns d cursor (peers cursor) resident positive
      ctx rfl ((tail.getLast?).or (some cursor)) 2 []
      {room := NLMSG_GOODSIZE-24-multiPeerSpace hp tail}
      (some (multiPeerParts hp tail).toArray)
    have spaces : multiPeerSpace hp tail = multiPeerSpace peers tail := (heldPeers_dump peers cursor tail).1
    have parts : multiPeerParts hp tail = multiPeerParts peers tail := (heldPeers_dump peers cursor tail).2
    have generation : (cursorAcquired d (some cursor)).deviceUpdateGen = d.deviceUpdateGen := heldGen
    simpa [R,ctx,cursorCallResult,generation,spaces,parts] using finish
  have body : Returns (cursorDumpBody held ctx 2 [] {room := NLMSG_GOODSIZE-20})
      (fun g => g.dev = some held) R := by
    apply cursorBody_loop_returns held ctx 2 [] _ R (by decide)
      (by intro id eq; cases eq; exact ⟨_,heldResident⟩) ?_ ?_
    · simp [cursorGuardValue,ctx,heldMembers,members,heldResident,live]
    · simpa [selected,Nat.sub_sub] using loop
  have call := cursorHeader_fresh_returns held ctx d.deviceUpdateGen
    (by simp [ctx]) (cursorDumpBody held ctx) (fun g => g.dev = some held) R
    (by simpa [cursorHeaderSkb,ctx,heldGen,NlSkb.put,nlmsgTotal,NLMSG_GOODSIZE] using body)
  intro g ambient device
  obtain ⟨result,final,after,run,post⟩ := call g ambient device
  refine ⟨result,final,after,?_,post⟩
  rw [wgGetDeviceDump_cursor_factor]
  simp [getDev,device]
  exact run

end Leanux.Proofs.WG.Config.TwoPage
