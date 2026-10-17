import Leanux.Proofs.WG.Config.MultiPeerDumpModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The original finite peer-loop step, including all split/cancelled branches. -/
def deviceDumpPeersStep (pid : PeerId)
    (state : DumpCtx × Option PeerId × NlSkb × Bool × Array PeerDumpAttrs) :
    WG.M (ForInStep (DumpCtx × Option PeerId × NlSkb × Bool × Array PeerDumpAttrs)) := do
  let (ctx, nextCursor, skb, done, ps) := state
  _ ← branch .dumpPeerIter true
  requireNotPending pid "dumping the peer"
  let (s,c,r) ← getPeerDump pid ctx skb
  match r with
  | .complete peer =>
    _ ← branch .dumpGetPeerFail false
    return .yield (c,some pid,s,done,ps.push peer)
  | .split peer =>
    _ ← branch .dumpGetPeerFail true
    return .done (c,nextCursor,s,false,ps.push peer)
  | .cancelled =>
    _ ← branch .dumpGetPeerFail true
    return .done (c,nextCursor,s,false,ps)

/-- Every listed resident with no allowed IPs completes under the supplied
finite buffer bound. The result preserves visit order and the whole Device. -/
theorem deviceDumpPeers_returns (d : Device) (peers : PeerId → Peer) (ids : List PeerId)
    (residents : ∀ pid ∈ ids, d.peers[pid]? = some (peers pid))
    (empty : ∀ pid ∈ ids, (peers pid).allowedipsList = [])
    (ctx : DumpCtx) (fresh : ctx.nextAllowedip = none) (seq : ctx.allowedipsSeq = 0)
    (cursor : Option PeerId) (skb : NlSkb) (prior : Array PeerDumpAttrs)
    (room : 168 * ids.length ≤ skb.room) :
    Returns (forIn ids (ctx,cursor,skb,true,prior) deviceDumpPeersStep)
      (fun g => g.dev = some d)
      (fun result g => g.dev = some d ∧ ∃ next,
        result = (ctx,next,{skb with room := skb.room - multiPeerSpace peers ids},true,
          prior ++ (multiPeerParts peers ids).toArray)) := by
  induction ids generalizing ctx cursor skb prior with
  | nil =>
    intro g ambient device
    refine ⟨_,g,ambient,rfl,device,cursor,?_⟩
    simp [multiPeerSpace,multiPeerParts]
  | cons pid ids ih =>
    intro g ambient device
    let first : Ambient := {ambient with steps := ambient.steps.push {
      decision := .dumpPeerIter,outcome := true,netRx := ambient.netRxSection}}
    have oneRoom : 168 ≤ skb.room := by simp only [List.length_cons] at room; omega
    obtain ⟨value,middle,after,run,same,valueEq⟩ :=
      getPeerDump_device_returns pid d (peers pid) (residents pid (by simp)) ctx skb
        fresh (empty pid (by simp)) oneRoom g first device
    have ctxEq : {ctx with nextAllowedip := none,allowedipsSeq := 0} = ctx := by
      cases ctx
      simp_all
    simp only [ctxEq] at valueEq
    subst value
    let inputs : Ambient := {after with steps := after.steps.push {
      decision := .dumpGetPeerFail,outcome := false,netRx := after.netRxSection}}
    have tailRoom : 168 * ids.length ≤ skb.room - peerFixedSpace (peers pid) := by
      have bound := peerFixedSpace_bound (peers pid)
      simp only [List.length_cons] at room
      omega
    obtain ⟨result,final,last,tailRun,finalDevice,next,resultEq⟩ :=
      ih (fun q member => residents q (by simp [member]))
        (fun q member => empty q (by simp [member])) ctx fresh seq (some pid)
        {skb with room := skb.room - peerFixedSpace (peers pid)}
        (prior.push {publicKey := hexKey (peers pid).remoteStatic,attrs := peerFixedAttrs (peers pid)})
        tailRoom middle inputs same
    refine ⟨result,final,last,?_,finalDevice,next,?_⟩
    · rw [List.forIn_cons]
      simp [deviceDumpPeersStep,branch,AmbientM.branch,requireNotPending]
      change (((getPeerDump pid ctx skb).run g).run first >>= _) = _
      rw [run]
      exact tailRun
    · have partsEq : prior.push {publicKey := hexKey (peers pid).remoteStatic, attrs := peerFixedAttrs (peers pid)} ++ (multiPeerParts peers ids).toArray =
          prior ++ (multiPeerParts peers (pid :: ids)).toArray := by
        change prior.push _ ++ (ids.map _).toArray = prior ++ ((_ :: ids.map _).toArray)
        rw [List.toArray_cons,Array.push_eq_append,Array.append_assoc]
      rw [partsEq] at resultEq
      simpa only [multiPeerSpace,List.map_cons,List.sum_cons,Nat.sub_sub] using resultEq

/-- Actual first-callback header, peer loop and NULL-cursor finalizer for a
nonempty fitting peer list. The arbitrary list may contain repeated peers. -/
theorem deviceDumpSource_multi_nonempty (d : Device) (peers : PeerId → Peer)
    (pid : PeerId) (ids : List PeerId) (members : d.peerList = pid :: ids)
    (residents : ∀ q ∈ pid :: ids, d.peers[q]? = some (peers q))
    (empty : ∀ q ∈ pid :: ids, (peers q).allowedipsList = [])
    (room : devicePrefixSpace d + 168 * (pid :: ids).length + 20 ≤ NLMSG_GOODSIZE) :
    Returns (deviceDumpSource d {hasWg := true} 0 {}) (fun g => g.dev = some d)
      (fun result g => result = multiPeerCall d peers (pid :: ids) ∧ g.dev = some d) := by
  generalize allEq : pid :: ids = all at members residents empty room ⊢
  have nonempty : all.isEmpty = false := by rw [← allEq]; rfl
  have positive : 0 < all.length := by rw [← allEq]; simp
  have n0 : nlaTotal 0 = 4 := rfl
  have n2 : nlaTotal 2 = 8 := rfl
  have n4 : nlaTotal 4 = 8 := rfl
  have n32 : nlaTotal 32 = 36 := rfl
  have rn : nlaTotal (d.ifname.length + 1) + 236 ≤ 3776 := by
    unfold devicePrefixSpace NLMSG_GOODSIZE at room
    omega
  have rname : ¬ 3732 < nlaTotal (d.ifname.length + 1) := by omega
  have r36 : ¬ 3732 - nlaTotal (d.ifname.length + 1) < 36 := by omega
  have r72 : ¬ 3696 - nlaTotal (d.ifname.length + 1) < 36 := by omega
  have rnest : ¬ 3660 - nlaTotal (d.ifname.length + 1) < 4 := by omega
  have rnest0 : ¬ 3732 - nlaTotal (d.ifname.length + 1) < 4 := by omega
  intro g ambient device
  let log (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision,outcome,netRx := a.netRxSection}}
  let front := log (log (log (log (log (log (log ambient
    .dumpNoHdr false) .dumpFirst true) .dumpPutPort false) .dumpPutFwmark false)
    .dumpPutIfindex false) .dumpPutIfname false) .dumpHasIdentity d.staticIdentity.hasIdentity
  let withIdentity := if d.staticIdentity.hasIdentity then
    log (log front .dumpPutPrivate false) .dumpPutPublic false else front
  let inputs := log (log (log withIdentity .dumpNoPeersNest false)
    .dumpPeerListEmpty false) .dumpCursorSet false
  let skb : NlSkb := {room := (if d.staticIdentity.hasIdentity then
    3656 - nlaTotal (d.ifname.length + 1) else 3728 - nlaTotal (d.ifname.length + 1))}
  have sufficient : 168 * all.length ≤ skb.room := by
    simp only [skb,devicePrefixSpace,NLMSG_GOODSIZE] at *
    split <;> split at room <;> omega
  obtain ⟨value,current,after,run,same,next,valueEq⟩ :=
    deviceDumpPeers_returns d peers all residents empty {hasWg := true} rfl rfl
      none skb #[] sufficient g inputs device
  subst value
  cases identity : d.staticIdentity.hasIdentity
  all_goals simp [deviceDumpSource, members, identity, branch, AmbientM.branch, WG.orM, WG.andM,
    NlSkb.put, nlmsgTotal, n0, n2, n4, n32, Nat.sub_sub, rname, r36, r72, rnest, rnest0, nonempty, requireNotPending]
  all_goals
    conv in (forIn all _ _) =>
      tactic =>
        exact show _ = (forIn all (({hasWg := true} : DumpCtx),none,skb,true,#[]) deviceDumpPeersStep) from by
          unfold deviceDumpPeersStep
          simp [skb,identity,branch,AmbientM.branch,requireNotPending]
          congr 2
    simp [skb,inputs,withIdentity,front,log,identity] at run
    simp only [skb,identity,Bool.false_eq_true,ite_false,ite_true]
    rw [run]
    refine ⟨_,current,⟨_,rfl⟩,?_,same⟩
    simp [multiPeerCall,deviceFixedAttrs,devicePrefixSpace,identity,
      NLMSG_GOODSIZE,Nat.sub_sub,nonempty]
    omega

/-- The actual empty-list branch cancels the peer nest and emits peers=none. -/
theorem deviceDumpSource_multi_empty (d : Device) (peers : PeerId → Peer)
    (members : d.peerList = []) (room : devicePrefixSpace d + 20 ≤ NLMSG_GOODSIZE) :
    Returns (deviceDumpSource d {hasWg := true} 0 {}) (fun g => g.dev = some d)
      (fun result g => result = multiPeerCall d peers [] ∧ g.dev = some d) := by
  have n0 : nlaTotal 0 = 4 := rfl
  have n2 : nlaTotal 2 = 8 := rfl
  have n4 : nlaTotal 4 = 8 := rfl
  have n32 : nlaTotal 32 = 36 := rfl
  intro g ambient device
  cases identity : d.staticIdentity.hasIdentity with
  | false =>
    have capacity := room
    simp only [devicePrefixSpace,identity,Bool.false_eq_true,ite_false,
      NLMSG_GOODSIZE] at capacity
    have rname : ¬ 3732 < nlaTotal (d.ifname.length + 1) := by omega
    have rnest : ¬ 3732 - nlaTotal (d.ifname.length + 1) < 4 := by omega
    simp [deviceDumpSource,members,identity,branch,AmbientM.branch,
      WG.orM,WG.andM,NlSkb.put,nlmsgTotal,n0,n2,n4,rname,rnest,Nat.sub_sub,peerPut]
    refine ⟨_,g,⟨_,rfl⟩,?_,device⟩
    simp [multiPeerCall,multiPeerSpace,deviceFixedAttrs,devicePrefixSpace,identity,
      NLMSG_GOODSIZE]
    omega
  | true =>
    have capacity := room
    simp only [devicePrefixSpace,identity,ite_true,
      NLMSG_GOODSIZE] at capacity
    have rname : ¬ 3732 < nlaTotal (d.ifname.length + 1) := by omega
    have r36 : ¬ 3732 - nlaTotal (d.ifname.length + 1) < 36 := by omega
    have r72 : ¬ 3696 - nlaTotal (d.ifname.length + 1) < 36 := by omega
    have rnest : ¬ 3660 - nlaTotal (d.ifname.length + 1) < 4 := by omega
    simp [deviceDumpSource,members,identity,branch,AmbientM.branch,
      WG.orM,WG.andM,NlSkb.put,nlmsgTotal,n0,n2,n4,n32,rname,r36,r72,rnest,Nat.sub_sub,peerPut]
    refine ⟨_,g,⟨_,rfl⟩,?_,device⟩
    simp [multiPeerCall,multiPeerSpace,deviceFixedAttrs,devicePrefixSpace,identity,
      NLMSG_GOODSIZE]
    omega

/-- The original dump callback completes a finite fitting list in one DATA
message. This is producer support; socket transport and the getter are separate. -/
theorem wgGetDeviceDump_multi (d : Device) (peers : PeerId → Peer)
    (residents : ∀ pid ∈ d.peerList, d.peers[pid]? = some (peers pid))
    (empty : ∀ pid ∈ d.peerList, (peers pid).allowedipsList = [])
    (room : devicePrefixSpace d + 168 * d.peerList.length + 20 ≤ NLMSG_GOODSIZE) :
    Returns (wgGetDeviceDump {hasWg := true} 0 {}) (fun g => g.dev = some d)
      (fun result g => result = multiPeerCall d peers d.peerList ∧ g.dev = some d) := by
  have callback : Returns (deviceDumpSource d {hasWg := true} 0 {})
      (fun g => g.dev = some d)
      (fun result g => result = multiPeerCall d peers d.peerList ∧ g.dev = some d) := by
    cases members : d.peerList with
    | nil => exact deviceDumpSource_multi_empty d peers members (by simpa [members] using room)
    | cons pid ids =>
      exact deviceDumpSource_multi_nonempty d peers pid ids members
        (by simpa [members] using residents) (by simpa [members] using empty)
        (by simpa [members] using room)
  rw [wgGetDeviceDump_source]
  intro g ambient device
  obtain ⟨result,final,after,run,value,same⟩ := callback g ambient device
  refine ⟨result,final,after,?_,value,same⟩
  simp [getDev,device]
  exact run

end Leanux.Proofs.WG.Config
