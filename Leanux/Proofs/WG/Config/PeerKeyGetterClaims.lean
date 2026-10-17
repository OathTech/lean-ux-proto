import Leanux.Proofs.WG.Config.PeerKeyGetterFrames
import Leanux.Proofs.WG.Config.KeyReadbackFrames
import Leanux.Proofs.WG.Config.PeerGetterClaims
import Leanux.Proofs.WG.Config.PeerPageCapacityFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Actual changed-key installation followed by canonical finite empty-IP peer
readback. Expiry clocks and stopped prefixes remain those of the original run.
The exact ordered installation relation describes the intermediate Device,
while the final Device includes the getter's ordered cursor handoffs. -/
theorem key_paginated_peers_get_after_set (d : Device) (peers : PeerId → Peer)
    (key : Key) (sock : NlSock)
    (established : d.staticIdentity.hasIdentity = true)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (emptyIps : ∀ q ∈ d.peerList, (peers q).allowedipsList = [])
    (headerFits : devicePrefixSpace (keyReadbackBase d key) ≤ NLMSG_GOODSIZE)
    (firstFits : ∀ q rest, d.peerList = q :: rest →
      peerFixedSpace (peers q) ≤ NLMSG_GOODSIZE-devicePrefixSpace (keyReadbackBase d key))
    (fresh : peerPageBoundaryFresh [] (peerPages peers (keyReadbackBase d key) d.peerList))
    (cursorData : PeerPageCursorData peers (peerPages peers (keyReadbackBase d key) d.peerList))
    (within : peerPageReceiveCount peers (keyReadbackBase d key) d.peerList ≤ 4096)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (privateKeyAttrs d key)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = (0,.ok (multiPeerJson (keyReadbackBase d key) peers)) ∧
        ∃ postSet observations values,
          ObservedKeyPeerRun false (keyReadbackBase d key) d.peerList observations postSet ∧
          (∀ q ∈ d.peerList, postSet.peers[q]? = some (values q)) ∧
          (∀ q, keyGetterPeerView (values q) = keyGetterPeerView (peers q)) ∧
          s.wg.device = some (peerGetterFinalDevice postSet values) ∧
          s.wg.nlSock7 = socketReadbackFinal sock postSet ∧
          CursorHeld postSet (peerGetterFinalDevice postSet values) none) := by
  intro entry ambient result final after pre run
  change (((wgSetDevice (privateKeyAttrs d key)).run entry).run ambient >>= fun ((ret,middle),next) =>
    ((wgGetDevice (byIndex d)).run middle).run next >>= fun ((dump,out),rest) =>
      Except.ok (((ret,dump),out),rest)) = _ at run
  cases setRun : ((wgSetDevice (privateKeyAttrs d key)).run entry).run ambient with
  | error stop => rw [setRun] at run; cases run
  | ok out =>
    obtain ⟨⟨ret,middle⟩,next⟩ := out
    have framed := setDevice_rotation_readbackFrame d key sock entry.fixtureNetDevices
      established changed absent entry ambient ret middle next
      ⟨pre.1,⟨pre.2.1,rfl⟩,pre.2.2⟩ setRun
    obtain ⟨code,current,observations,device,effect⟩ :=
      setDevice_private_changed_no_collision d key changed absent
        entry ambient ret middle next ⟨pre.1,pre.2.2⟩ setRun
    have quiet : requestsStagedSend d key = false := by simp [requestsStagedSend,established]
    rw [quiet] at effect
    change ObservedKeyPeerRun false (keyReadbackBase d key) d.peerList observations current at effect
    obtain ⟨fields,lookup⟩ := observedKeyPeerRun_getter_frame _ current _ observations effect
    let values := keyGetterPeers (keyReadbackBase d key) current peers
    have baseResidents : ∀ q ∈ (keyReadbackBase d key).peerList,
        (keyReadbackBase d key).peers[q]? = some (peers q) := by
      simpa only [keyReadbackBase,installedDevice,requestGeneration,cookieKeysAfter] using residents
    obtain ⟨currentResidents,same⟩ := keyGetterPeers_frame _ current peers lookup baseResidents
    change (∀ q ∈ d.peerList, current.peers[q]? = some (values q)) at currentResidents
    change (∀ q, keyGetterPeerView (values q) = keyGetterPeerView (peers q)) at same
    have details (q : PeerId) :
        (values q).remoteStatic = (peers q).remoteStatic ∧
        peerFixedAttrs (values q) = peerFixedAttrs (peers q) ∧
        peerFixedSpace (values q) = peerFixedSpace (peers q) ∧
        (values q).allowedipsList = (peers q).allowedipsList ∧
        (values q).refcount = (peers q).refcount ∧
        (values q).isDead = (peers q).isDead := by
      simpa only [keyGetterPeerView,Prod.mk.injEq] using same q
    have members : current.peerList = d.peerList := by
      have h := congrArg Device.peerList fields
      exact h
    have space : devicePrefixSpace current = devicePrefixSpace (keyReadbackBase d key) :=
      by have h := congrArg devicePrefixSpace fields; exact h
    have index : current.ifindex = d.ifindex := by
      have h := congrArg Device.ifindex fields
      exact h
    have name : current.ifname = d.ifname := by
      have h := congrArg Device.ifname fields
      exact h
    have attrs : deviceFixedAttrs current = deviceFixedAttrs (keyReadbackBase d key) :=
      by have h := congrArg deviceFixedAttrs fields; exact h
    obtain ⟨plan,count,lifetime⟩ := peerPage_inputs_congr (keyReadbackBase d key) current peers values
      space (fun q => (details q).2.2.1) (fun q => (details q).2.2.2.2.2)
      (fun q => (details q).2.2.2.2.1) d.peerList
    have selection : selectsDevice middle current := by
      have original : selectsDevice entry d := pre.2.2
      simpa [selectsDevice,framed.2,index,name] using original
    obtain ⟨dump,out,rest,getRun,dumped,finalDevice,finalSocket,held⟩ :=
      peer_getter_returns current values sock
        (by simpa only [members] using currentResidents)
        (by intro q member; rw [(details q).2.2.2.1]; exact emptyIps q (members ▸ member))
        (by simpa only [space] using headerFits)
        (by intro q tail list; simpa only [space,(details q).2.2.1] using firstFits q tail (members.symm.trans list))
        (by simpa only [members,plan] using fresh)
        (by rw [members]; exact lifetime.mpr cursorData)
        idle emptyQueue (by simpa only [members,count] using within)
        middle next ⟨device,framed.1,selection⟩
    have selector : byIndex d = byIndex current := by simp [byIndex,index]
    rw [setRun] at run
    change (((wgGetDevice (byIndex d)).run middle).run next >>= fun ((dump,out),rest) =>
      Except.ok (((ret,dump),out),rest)) = _ at run
    rw [selector,getRun] at run
    cases run
    have parts : multiPeerParts values current.peerList = multiPeerParts peers d.peerList := by
      unfold multiPeerParts
      rw [members]
      apply List.map_congr_left
      intro q _
      simp only [(details q).1,(details q).2.1]
    have json : multiPeerJson current values = multiPeerJson (keyReadbackBase d key) peers := by
      simp only [multiPeerJson,attrs,parts]
      rfl
    exact ⟨by simp [code,dumped,json], current,observations,values,effect,
      currentResidents,same,finalDevice,finalSocket,held⟩

end Leanux.Proofs.WG.Config
