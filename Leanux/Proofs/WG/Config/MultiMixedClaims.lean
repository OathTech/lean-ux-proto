import Leanux.Proofs.WG.Config.MultiMixedSource
import Leanux.Proofs.WG.Config.MultiMixedFrames
import Leanux.Proofs.WG.Config.MultiPeerGetterClaims
import Leanux.Proofs.WG.Config.MultiPeerScalarModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Whole mixed set/get over a fitting finite peer list. Clears follow the
actual captured list, including repeated visits; a malformed second request
retains the mark and first scalar write. Hidden reset Stops are not excluded
by a readiness assumption and do not become normal returns. -/
theorem multi_mixed_fitting_get_after_set (d : Device) (peers : PeerId → Peer)
    (mark : Nat) (key psk : Key) (interval : Nat) (bad : Bool) (pid : PeerId) (sock : NlSock)
    (net : d.creatingNet = true)
    (found : d.peerHashtable.find? (·.1 == key) = some (key,pid))
    (resident : d.peers[pid]? = some (peers pid))
    (live : 0 < (peers pid).refcount) (bounded : (peers pid).refcount + 1 < 2 ^ 31)
    (down : d.running = false)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (emptyIps : ∀ q ∈ d.peerList, (peers q).allowedipsList = [])
    (room : devicePrefixSpace d + 168 * d.peerList.length + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        result = ((if bad then -EINVAL else 0),.ok
          (multiPeerJson (mixedFwmarkBase d mark) (scalarPeerView peers pid psk interval))) ∧
        s.wg.nlSock7 = {sock with queue := [],ctx := {hasWg := true},prevSeq := d.deviceUpdateGen + 1,dumpDoneErrno := 0,cbRunning := false} ∧
        ∃ current, s.wg.device = some current ∧ MultiMixedEffect d mark pid psk interval current) := by
  intro entry ambient result final after pre run
  change (((wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)).run entry).run ambient >>=
    fun ((ret,middle),next) => ((wgGetDevice (byIndex d)).run middle).run next >>=
      fun ((dump,out),rest) => Except.ok (((ret,dump),out),rest)) = _ at run
  cases setRun : ((wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)).run entry).run ambient with
  | error stop => rw [setRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨ret,middle⟩,next⟩ := pair
    obtain ⟨code,framed,current,device,effect⟩ := setDevice_multi_mixed d mark key psk interval bad pid (peers pid)
      sock entry.fixtureNetDevices net found resident live bounded down
      entry ambient ret middle next ⟨pre.1,⟨pre.2.1,rfl⟩,pre.2.2⟩ setRun
    have outer := multiMixedEffect_outer d current mark pid psk interval effect
    have sameList : current.peerList = d.peerList := by
      have h := congrArg Device.peerList outer
      exact h
    have sameName : current.ifname = d.ifname := by
      have h := congrArg Device.ifname outer
      exact h
    have sameIndex : current.ifindex = d.ifindex := by
      have h := congrArg Device.ifindex outer
      exact h
    have sameSpace : devicePrefixSpace current = devicePrefixSpace d := by
      have h := congrArg devicePrefixSpace outer
      exact h
    have generation : current.deviceUpdateGen = d.deviceUpdateGen + 1 := by
      have h := congrArg Device.deviceUpdateGen outer
      exact h
    let values : PeerId → Peer := fun q => (current.peers[q]?).getD (peers q)
    have facts : ∀ q ∈ d.peerList, current.peers[q]? = some (values q) ∧
        (values q).allowedipsList = [] ∧ (values q).remoteStatic = (peers q).remoteStatic ∧
        peerFixedAttrs (values q) = peerFixedAttrs (scalarPeerView peers pid psk interval q) := by
      intro q member
      obtain ⟨value,lookup,noIps,remote,attrs⟩ :=
        multiMixedEffect_peer d current mark pid q psk interval (peers q) effect (residents q member)
      have same : values q = value := by simp only [values,lookup,Option.getD_some]
      refine ⟨?_,?_,?_,?_⟩
      · simpa only [same] using lookup
      · exact same ▸ noIps.trans (emptyIps q member)
      · exact same ▸ remote
      · by_cases equal : q = pid
        · subst q
          simpa only [same,scalarPeerView,ite_true] using attrs
        · simpa only [same,scalarPeerView,equal,ite_false] using attrs
    have currentResidents : ∀ q ∈ current.peerList, current.peers[q]? = some (values q) := by
      intro q member
      exact (facts q (sameList ▸ member)).1
    have currentEmpty : ∀ q ∈ current.peerList, (values q).allowedipsList = [] := by
      intro q member
      exact (facts q (sameList ▸ member)).2.1
    have currentRoom : devicePrefixSpace current + 168 * current.peerList.length + 20 ≤ NLMSG_GOODSIZE := by
      simpa only [sameList,sameSpace] using room
    have selection : selectsDevice middle current := by
      have selected : selectsDevice entry d := pre.2.2
      simpa only [selectsDevice,sameName,sameIndex,framed.2] using selected
    obtain ⟨dump,out,rest,getRun,dumped,retained,socket⟩ := fitting_peers_getter_returns current values sock
      currentResidents currentEmpty currentRoom idle emptyQueue middle next ⟨device,framed.1,selection⟩
    have selector : byIndex d = byIndex current := by simp only [byIndex,sameIndex]
    rw [setRun] at run
    change (((wgGetDevice (byIndex d)).run middle).run next >>=
      fun ((dump,out),rest) => Except.ok (((ret,dump),out),rest)) = _ at run
    rw [selector,getRun] at run
    cases run
    have attrs : deviceFixedAttrs current = deviceFixedAttrs (mixedFwmarkBase d mark) := by
      have h := congrArg deviceFixedAttrs outer
      exact h
    have parts : multiPeerParts values current.peerList =
        multiPeerParts (scalarPeerView peers pid psk interval) d.peerList := by
      simp only [multiPeerParts,sameList]
      apply List.map_congr_left
      intro q member
      have observed := facts q member
      simp only [observed.2.2.1,observed.2.2.2,scalarPeerView]
      split
      · rename_i equal
        subst q
        rfl
      · rfl
    have json : multiPeerJson current values =
        multiPeerJson (mixedFwmarkBase d mark) (scalarPeerView peers pid psk interval) := by
      simp only [multiPeerJson,parts,attrs,mixedFwmarkBase]
    refine ⟨?_,?_,current,retained,effect⟩
    · simp only [code,dumped,json]
    · change final.nlSock7 = _
      change final.nlSock7 = socketReadbackFinal sock current at socket
      simpa only [socketReadbackFinal,generation] using socket

end Leanux.Proofs.WG.Config
