import Leanux.Proofs.WG.Config.TwoPageCallbackSource
import Leanux.Proofs.WG.Config.TwoPageDrainSource
import Leanux.Proofs.WG.Config.TwoPageCoalesceClaims
import Leanux.Proofs.WG.Config.MultiPeerGetterModel
import Leanux.Proofs.WG.Config.ClaimView

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The original getter emits two DATA pages of complete empty-IP peers and
then successful DONE, inline or separate according to actual remaining room.
The boundary is the cursor's first list occurrence; later duplicates and
arbitrary endpoint encodings retain their source serialization. Reference
bounds apply only to the held cursor. All actual callbacks and receives are
derived, rather than assumed. The final Device retains both actual tree writes. -/
theorem two_pages_getter_returns (d : Device) (peers : PeerId → Peer) (sock : NlSock)
    (before : List PeerId) (cursor next : PeerId) (tail : List PeerId)
    (members : d.peerList = (before ++ [cursor]) ++ next :: tail)
    (fresh : cursor ∉ before)
    (residents : ∀ pid ∈ d.peerList, d.peers[pid]? = some (peers pid))
    (emptyIps : ∀ pid ∈ d.peerList, (peers pid).allowedipsList = [])
    (live : (peers cursor).isDead = false)
    (positive : 0 < (peers cursor).refcount) (bounded : (peers cursor).refcount+1 < 2^31)
    (firstFits : devicePrefixSpace d + multiPeerSpace peers (before ++ [cursor]) ≤ NLMSG_GOODSIZE)
    (firstFull : NLMSG_GOODSIZE < devicePrefixSpace d + multiPeerSpace peers (before ++ [cursor]) + peerFixedSpace (peers next))
    (lastFits : 24 + multiPeerSpace peers (next::tail) ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = .ok (multiPeerJson d peers) ∧
        s.wg.device = some (cursorReleased (cursorAcquired d (some cursor)) (some cursor)) ∧
        s.wg.nlSock7 = socketReadbackFinal sock d) := by
  let front := before ++ [cursor]
  let rest := next :: tail
  let held := cursorAcquired d (some cursor)
  let released := cursorReleased held (some cursor)
  have resident : d.peers[cursor]? = some (peers cursor) := residents cursor (by simp [members])
  have heldGen : held.deviceUpdateGen = d.deviceUpdateGen := by simp [held,cursorAcquired,resident]
  have releasedGen : released.deviceUpdateGen = d.deviceUpdateGen := by
    have outer := (TwoPage.cursorHeld_device_fields d cursor (peers cursor) resident positive).2
    have fields := congrArg Device.deviceUpdateGen outer
    exact fields
  have headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE := by omega
  have header : cursorHeaderSkb d {hasWg := true} {} =
      {room := NLMSG_GOODSIZE-(devicePrefixSpace d-4)} := by
    cases identity : d.staticIdentity.hasIdentity with
    | false =>
      simp only [devicePrefixSpace,identity,Bool.false_eq_true,ite_false,NLMSG_GOODSIZE] at headerFits
      have name : ¬3732 < nlaTotal (d.ifname.length+1) := by omega
      simp [cursorHeaderSkb,NlSkb.put,nlmsgTotal,identity,devicePrefixSpace,
        show nlaTotal 2 = 8 from rfl,show nlaTotal 4 = 8 from rfl,name,NLMSG_GOODSIZE]
      omega
    | true =>
      simp only [devicePrefixSpace,identity,ite_true,NLMSG_GOODSIZE] at headerFits
      have name : ¬3732 < nlaTotal (d.ifname.length+1) := by omega
      have priv : ¬3732-nlaTotal (d.ifname.length+1) < 36 := by omega
      have pub : ¬3696-nlaTotal (d.ifname.length+1) < 36 := by omega
      simp [cursorHeaderSkb,NlSkb.put,nlmsgTotal,identity,devicePrefixSpace,
        show nlaTotal 2 = 8 from rfl,show nlaTotal 4 = 8 from rfl,
        show nlaTotal 32 = 36 from rfl,name,priv,pub,NLMSG_GOODSIZE,Nat.sub_sub]
      omega
  have prefixLower : 48 ≤ devicePrefixSpace d := by unfold devicePrefixSpace; omega
  have nest : 4 ≤ (cursorHeaderSkb d {hasWg := true} {}).room := by rw [header]; dsimp; omega
  have room : (cursorHeaderSkb d {hasWg := true} {}).room-4 = NLMSG_GOODSIZE-devicePrefixSpace d := by
    rw [header]; dsimp; omega
  let first : DumpCall := {ret := Int.ofNat (NLMSG_GOODSIZE-(NLMSG_GOODSIZE-devicePrefixSpace d-multiPeerSpace peers front)), ctx := {hasWg := true,nextPeer := some cursor},prevSeq := d.deviceUpdateGen, skb := {room := NLMSG_GOODSIZE-devicePrefixSpace d-multiPeerSpace peers front, messages := [.data 2 (deviceFixedAttrs d) (some (multiPeerParts peers front))]}}
  let last : DumpCall := {ret := 0,ctx := {hasWg := true},prevSeq := d.deviceUpdateGen, skb := {room := NLMSG_GOODSIZE-24-multiPeerSpace peers rest,messages := [.data 2 [] (some (multiPeerParts peers rest))]}}
  have firstRun : Returns (wgGetDeviceDump {hasWg := true} 0 {})
      (fun g => g.dev = some d) (fun result g => result = first ∧ g.dev = some held) := by
    have run := TwoPage.first_callback_returns d peers before cursor next tail members residents emptyIps
      headerFits nest (by rw [room]; omega) (by rw [room]; omega) positive bounded
    have subtraction : NLMSG_GOODSIZE-(devicePrefixSpace d-4)-4 = NLMSG_GOODSIZE-devicePrefixSpace d := by omega
    simpa [first,front,held,cursorCallResult,header,subtraction] using run
  have more : 0 < first.ret := by
    change (0 : Int) < Int.ofNat (NLMSG_GOODSIZE-(NLMSG_GOODSIZE-devicePrefixSpace d-multiPeerSpace peers front))
    apply Int.natCast_pos.mpr
    dsimp only [front]
    omega
  have lastRun : Returns (wgGetDeviceDump first.ctx first.prevSeq {})
      (fun g => g.dev = some held) (fun result g => result = last ∧ g.dev = some released) := by
    exact TwoPage.resumed_callback_returns d peers before (next::tail) cursor
      (by simpa only [List.append_assoc,List.singleton_append] using members)
      fresh residents emptyIps live positive (by omega)
  let current : NlSock := {sock with cbRunning := true,ctx := first.ctx,prevSeq := first.prevSeq, dumpDoneErrno := first.ret,queue := [first.skb]}
  have start : Returns (netlinkDumpStart 7 (byIndex d))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
      (fun _ g => g.dev = some held ∧ g.nlSock7 = current) := by
    simpa [current,emptyQueue] using
      netlinkDumpStart_more_device_transition d held sock first idle more firstRun
  have receive : Returns (netlinkRecvmsg 7)
      (fun g => g.dev = some held ∧ g.nlSock7 = current)
      (fun result g => result = some [.data 2 (deviceFixedAttrs d) (some (multiPeerParts peers front))] ∧
        g.dev = some released ∧ g.nlSock7 = paginationCompletedSocket current last) := by
    simpa [first] using netlinkRecvmsg_completing_device_transition held released current first.skb last
      rfl rfl more rfl rfl lastRun
  have coalesced : coalesce [.data 2 (deviceFixedAttrs d) (some (multiPeerParts peers front)),
      .data 2 [] (some (multiPeerParts peers rest)),.done 2 0] = pure (.ok (multiPeerJson d peers)) := by
    simpa [multiPeerJson,members,front,rest] using coalesce_two_complete_pages d peers front rest
  have drain := getterDrain_two_pages_source held released current current last
    (deviceFixedAttrs d) [] (some (multiPeerParts peers front)) (some (multiPeerParts peers rest))
    (multiPeerJson d peers) rfl rfl (by simpa [last] using releasedGen.symm) rfl receive coalesced
  change Returns (wgGetDevice (byIndex d))
    (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
    (fun result g => result = .ok (multiPeerJson d peers) ∧ g.dev = some released ∧
      g.nlSock7 = socketReadbackFinal sock d)
  rw [wgGetDevice_source]
  apply returns_bind _ _ start
  intro value g ambient pre
  obtain ⟨result,final,after,run,json,device,socket⟩ := drain g ambient pre
  refine ⟨result,final,after,run,json,device,?_⟩
  simpa [socketReadbackFinal,current,releasedGen] using socket

end Leanux.Proofs.WG.Config
