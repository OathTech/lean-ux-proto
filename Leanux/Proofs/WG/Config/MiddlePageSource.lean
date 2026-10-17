import Leanux.Proofs.WG.Config.MiddlePageEffects
import Leanux.Proofs.WG.Config.TwoPageCallbackSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Total actual finalizer for an already-held old cursor. The next reference
is acquired before releasing the old one; final completion acquires none. -/
theorem cursorFinish_handoff_returns (d : Device) (old : PeerId) (p : Peer)
    (resident : d.peers[old]? = some p) (retained : 1 < p.refcount)
    (ctx : DumpCtx) (oldCursor : ctx.nextPeer = some old) (next : Option PeerId) (done : Bool)
    (ready : done = false → ∃ id q, next = some id ∧ id ≠ old ∧
      d.peers[id]? = some q ∧ 0 < q.refcount ∧ q.refcount+1 < 2^31)
    (flags : Nat) (attrs : List (String × Json)) (skb : NlSkb) (parts : Option (Array PeerDumpAttrs)) :
    Returns (cursorDumpFinish d flags attrs ctx next skb done parts)
      (fun g => g.dev = some d)
      (fun result g => result = cursorCallResult d flags attrs ctx next skb done parts ∧
        g.dev = some (cursorHandoff d (some old) (if done then none else next))) := by
  have notLast : p.refcount ≠ 1 := by omega
  let mark (a : Ambient) (site : Decision) (value : Bool) : Ambient :=
    {a with steps := a.steps.push {decision := site,outcome := value,netRx := a.netRxSection}}
  cases done with
  | false =>
    obtain ⟨id,q,nextEq,different,found,positive,bounded⟩ := ready rfl
    subst next
    let acquired := cursorAcquired d (some id)
    have oldAfter : acquired.peers[old]? = some p := by
      simp [acquired,cursorAcquired,found,Std.TreeMap.getElem?_insert,different,resident]
    have put : Returns (peerPut (some old)) (fun g => g.dev = some acquired)
        (fun _ g => g.dev = some (cursorHandoff d (some old) (some id))) := by
      have actual := (returns_iff _ _ _).mpr
        (peerPut_retained_returns old acquired p oldAfter retained)
      have after : (cursorAcquired d (some id)).peers[old]? = some p := oldAfter
      simpa [cursorHandoff,cursorReleased,after,notLast,Index.releasedPeerDevice,withPeer] using actual
    intro g ambient device
    let before := mark (mark (mark ambient .dumpOutRetZero true) .dumpOutNotDone true) .dumpOutHasCursor true
    obtain ⟨value,middle,inputs,getRun,midDevice⟩ := TwoPage.peerGet_returns id d q found positive bounded g before device
    cases value
    obtain ⟨value,final,after,putRun,post⟩ := put middle inputs midDevice
    cases value
    let remaining := mark (mark after .dumpRetErr false) .dumpDone false
    refine ⟨cursorCallResult d flags attrs ctx (some id) skb false parts,final,remaining,?_,rfl,post⟩
    simp [cursorDumpFinish,WG.andM,branch,AmbientM.branch]
    change (((peerGet id).run g).run before >>= _) = _
    rw [getRun]
    change (((peerPut ctx.nextPeer).run middle).run inputs >>= _) = _
    rw [oldCursor,putRun]
    simp [cursorCallResult,remaining,mark]
  | true =>
    have put : Returns (peerPut (some old)) (fun g => g.dev = some d)
        (fun _ g => g.dev = some (cursorHandoff d (some old) none)) := by
      have actual := (returns_iff _ _ _).mpr (peerPut_retained_returns old d p resident retained)
      simpa [cursorHandoff,cursorReleased,cursorAcquired,resident,notLast,Index.releasedPeerDevice,withPeer] using actual
    intro g ambient device
    let before := mark (mark ambient .dumpOutRetZero true) .dumpOutNotDone false
    obtain ⟨value,final,after,run,post⟩ := put g before device
    cases value
    let remaining := mark (mark after .dumpRetErr false) .dumpDone true
    refine ⟨cursorCallResult d flags attrs ctx next skb true parts,final,remaining,?_,rfl,post⟩
    simp [cursorDumpFinish,WG.andM,branch,AmbientM.branch,oldCursor]
    change (((peerPut (some old)).run g).run before >>= _) = _
    rw [run]
    simp [cursorCallResult,remaining,mark]

/-- An actual nonfinal resumed callback on the accumulated Device. It emits
a maximal completed prefix, acquires the new boundary, then releases the old
boundary. The boundary-reference inputs are ordinary baseline peer data. -/
theorem cursorPage_nonfinal_returns (base current : Device) (peers : PeerId → Peer)
    (before front : List PeerId) (old next bad : PeerId) (tail : List PeerId)
    (held : CursorHeld base current (some old))
    (members : base.peerList = before ++ old :: ((front ++ [next]) ++ bad :: tail))
    (fresh : old ∉ before) (different : next ≠ old)
    (residents : ∀ id ∈ base.peerList, base.peers[id]? = some (peers id))
    (empty : ∀ id ∈ base.peerList, (peers id).allowedipsList = [])
    (live : (peers old).isDead = false) (oldPositive : 0 < (peers old).refcount)
    (newPositive : 0 < (peers next).refcount) (bounded : (peers next).refcount+1 < 2^31)
    (fits : multiPeerSpace peers (front ++ [next]) ≤ NLMSG_GOODSIZE-24)
    (short : NLMSG_GOODSIZE-24-multiPeerSpace peers (front ++ [next]) < peerFixedSpace (peers bad)) :
    Returns (wgGetDeviceDump {hasWg := true,nextPeer := some old} base.deviceUpdateGen {})
      (fun g => g.dev = some current)
      (fun result g => result = cursorCallResult base 2 [] {hasWg := true,nextPeer := some old}
        (some next) {room := NLMSG_GOODSIZE-24-multiPeerSpace peers (front ++ [next])}
        false (some (multiPeerParts peers (front ++ [next])).toArray) ∧
        g.dev = some (cursorHandoff current (some old) (some next))) := by
  let ctx : DumpCtx := {hasWg := true,nextPeer := some old}
  let hp := TwoPage.heldPeers peers old
  let ids := (front ++ [next]) ++ bad :: tail
  have baseOld : base.peers[old]? = some (peers old) := residents old (by simp [members])
  have oldAt : current.peers[old]? = some {peers old with refcount := (peers old).refcount+1} := by
    simpa [baseOld] using held.2 old
  have listEq : current.peerList = base.peerList := by
    have fact := congrArg Device.peerList held.1; exact fact
  have generation : current.deviceUpdateGen = base.deviceUpdateGen := by
    have fact := congrArg Device.deviceUpdateGen held.1; exact fact
  have selected : cursorSelected current ctx = ids :=
    TwoPage.cursorSelected_boundary current before ids old (listEq.trans members) fresh
  have memberBase (id : PeerId) (member : id ∈ ids) : id ∈ base.peerList := by
    rw [members]
    exact List.mem_append_right before (List.mem_cons_of_mem old member)
  have reads : ∀ id ∈ ids, current.peers[id]? = some (hp id) := by
    intro id member
    have found := residents id (memberBase id member)
    by_cases same : id = old
    · subst id; simpa [hp,TwoPage.heldPeers] using oldAt
    · simpa [found,hp,TwoPage.heldPeers,same,Ne.symm same] using held.2 id
  have noIps : ∀ id ∈ ids, (hp id).allowedipsList = [] := by
    intro id member
    have no := empty id (memberBase id member)
    simp only [hp,TwoPage.heldPeers]
    split <;> exact no
  have spaces : multiPeerSpace hp (front ++ [next]) = multiPeerSpace peers (front ++ [next]) :=
    (TwoPage.heldPeers_dump peers old (front ++ [next])).1
  have parts : multiPeerParts hp (front ++ [next]) = multiPeerParts peers (front ++ [next]) :=
    (TwoPage.heldPeers_dump peers old (front ++ [next])).2
  have badSpace : peerFixedSpace (hp bad) = peerFixedSpace (peers bad) := by
    dsimp [hp,TwoPage.heldPeers]; split <;> rfl
  have nextAt : current.peers[next]? = some (peers next) := by
    simpa [hp,TwoPage.heldPeers,different] using reads next (by simp [ids])
  let R : DumpCall → WGWorld → Prop := fun result g => result =
      cursorCallResult base 2 [] ctx (some next)
        {room := NLMSG_GOODSIZE-24-multiPeerSpace peers (front ++ [next])}
        false (some (multiPeerParts peers (front ++ [next])).toArray) ∧
      g.dev = some (cursorHandoff current (some old) (some next))
  have loop : Returns (cursorLoopFinish current ids ctx 2 [] {room := NLMSG_GOODSIZE-24})
      (fun g => g.dev = some current) R := by
    apply TwoPage.cursorLoopFinish_returns current hp ids ctx 2 [] _ reads noIps rfl R
    dsimp only
    rw [fixedPeersRun_resumed_split hp front next bad tail ctx (some old) _ rfl rfl
      (by simpa [spaces] using fits) (by simpa [spaces,badSpace] using short)]
    have finish := cursorFinish_handoff_returns current old
      {peers old with refcount := (peers old).refcount+1} oldAt (by dsimp; omega)
      ctx rfl (some next) false
      (by intro _; exact ⟨next,peers next,rfl,different,nextAt,newPositive,bounded⟩)
      2 [] {room := NLMSG_GOODSIZE-24-multiPeerSpace hp (front ++ [next])}
      (some (multiPeerParts hp (front ++ [next])).toArray)
    simpa [R,cursorCallResult,generation,spaces,parts] using finish
  have body : Returns (cursorDumpBody current ctx 2 [] {room := NLMSG_GOODSIZE-20})
      (fun g => g.dev = some current) R := by
    apply TwoPage.cursorBody_loop_returns current ctx 2 [] _ R (by decide)
      (by intro id eq; cases eq; exact ⟨_,oldAt⟩) ?_ ?_
    · simp [cursorGuardValue,ctx,listEq,members,oldAt,live]
    · simpa [selected,Nat.sub_sub] using loop
  have call := TwoPage.cursorHeader_fresh_returns current ctx base.deviceUpdateGen
    (by simp [ctx]) (cursorDumpBody current ctx) (fun g => g.dev = some current) R
    (by simpa [cursorHeaderSkb,ctx,generation,NlSkb.put,nlmsgTotal,NLMSG_GOODSIZE] using body)
  intro g ambient device
  obtain ⟨result,final,after,run,post⟩ := call g ambient device
  refine ⟨result,final,after,?_,post⟩
  rw [wgGetDeviceDump_cursor_factor]
  simp [getDev,device]
  exact run

/-- The actual last resumed callback releases its held cursor after emitting
all remaining fitting peer occurrences, including an empty selected suffix. -/
theorem cursorPage_final_returns (base current : Device) (peers : PeerId → Peer)
    (before ids : List PeerId) (old : PeerId)
    (held : CursorHeld base current (some old))
    (members : base.peerList = before ++ old :: ids) (fresh : old ∉ before)
    (residents : ∀ id ∈ base.peerList, base.peers[id]? = some (peers id))
    (empty : ∀ id ∈ base.peerList, (peers id).allowedipsList = [])
    (live : (peers old).isDead = false) (positive : 0 < (peers old).refcount)
    (fits : multiPeerSpace peers ids ≤ NLMSG_GOODSIZE-24) :
    Returns (wgGetDeviceDump {hasWg := true,nextPeer := some old} base.deviceUpdateGen {})
      (fun g => g.dev = some current)
      (fun result g => result = {ret := 0,ctx := {hasWg := true},prevSeq := base.deviceUpdateGen, skb := {room := NLMSG_GOODSIZE-24-multiPeerSpace peers ids, messages := [.data 2 [] (some (multiPeerParts peers ids))]}} ∧
        g.dev = some (cursorHandoff current (some old) none)) := by
  let ctx : DumpCtx := {hasWg := true,nextPeer := some old}
  let hp := TwoPage.heldPeers peers old
  have baseOld : base.peers[old]? = some (peers old) := residents old (by simp [members])
  have oldAt : current.peers[old]? = some {peers old with refcount := (peers old).refcount+1} := by
    simpa [baseOld] using held.2 old
  have listEq : current.peerList = base.peerList := by
    have fact := congrArg Device.peerList held.1; exact fact
  have generation : current.deviceUpdateGen = base.deviceUpdateGen := by
    have fact := congrArg Device.deviceUpdateGen held.1; exact fact
  have selected : cursorSelected current ctx = ids :=
    TwoPage.cursorSelected_boundary current before ids old (listEq.trans members) fresh
  have memberBase (id : PeerId) (member : id ∈ ids) : id ∈ base.peerList := by simp [members,member]
  have reads : ∀ id ∈ ids, current.peers[id]? = some (hp id) := by
    intro id member
    have found := residents id (memberBase id member)
    by_cases same : id = old
    · subst id; simpa [hp,TwoPage.heldPeers] using oldAt
    · simpa [found,hp,TwoPage.heldPeers,same,Ne.symm same] using held.2 id
  have noIps : ∀ id ∈ ids, (hp id).allowedipsList = [] := by
    intro id member
    have no := empty id (memberBase id member)
    simp only [hp,TwoPage.heldPeers]
    split <;> exact no
  have spaces : multiPeerSpace hp ids = multiPeerSpace peers ids := (TwoPage.heldPeers_dump peers old ids).1
  have parts : multiPeerParts hp ids = multiPeerParts peers ids := (TwoPage.heldPeers_dump peers old ids).2
  let R : DumpCall → WGWorld → Prop := fun result g => result =
      {ret := 0,ctx := {hasWg := true},prevSeq := base.deviceUpdateGen, skb := {room := NLMSG_GOODSIZE-24-multiPeerSpace peers ids, messages := [.data 2 [] (some (multiPeerParts peers ids))]}} ∧
      g.dev = some (cursorHandoff current (some old) none)
  have loop : Returns (cursorLoopFinish current ids ctx 2 [] {room := NLMSG_GOODSIZE-24})
      (fun g => g.dev = some current) R := by
    apply TwoPage.cursorLoopFinish_returns current hp ids ctx 2 [] _ reads noIps rfl R
    dsimp only
    rw [TwoPage.fixedPeersRun_complete hp ids ctx rfl rfl (some old) _ #[] (by simpa [spaces] using fits)]
    have finish := cursorFinish_handoff_returns current old
      {peers old with refcount := (peers old).refcount+1} oldAt (by dsimp; omega)
      ctx rfl ((ids.getLast?).or (some old)) true (by intro impossible; cases impossible)
      2 [] {room := NLMSG_GOODSIZE-24-multiPeerSpace hp ids} (some (multiPeerParts hp ids).toArray)
    simpa [R,ctx,cursorCallResult,generation,spaces,parts] using finish
  have body : Returns (cursorDumpBody current ctx 2 [] {room := NLMSG_GOODSIZE-20})
      (fun g => g.dev = some current) R := by
    apply TwoPage.cursorBody_loop_returns current ctx 2 [] _ R (by decide)
      (by intro id eq; cases eq; exact ⟨_,oldAt⟩) ?_ ?_
    · simp [cursorGuardValue,ctx,listEq,members,oldAt,live]
    · simpa [selected,Nat.sub_sub] using loop
  have call := TwoPage.cursorHeader_fresh_returns current ctx base.deviceUpdateGen
    (by simp [ctx]) (cursorDumpBody current ctx) (fun g => g.dev = some current) R
    (by simpa [cursorHeaderSkb,ctx,generation,NlSkb.put,nlmsgTotal,NLMSG_GOODSIZE] using body)
  intro g ambient device
  obtain ⟨result,final,after,run,post⟩ := call g ambient device
  refine ⟨result,final,after,?_,post⟩
  rw [wgGetDeviceDump_cursor_factor]
  simp [getDev,device]
  exact run

end Leanux.Proofs.WG.Config
