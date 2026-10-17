import Leanux.Proofs.WG.Config.MixedGetterInputFrames
import Leanux.Proofs.WG.Config.PeerKeyGetterFrames
import Leanux.Proofs.WG.Config.KeyReadbackFrames
import Leanux.Proofs.WG.Config.MixedGetterClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Actual established-identity key installation followed by full finite
mixed peer/allowed-IP pagination. The observed ordered expiry effects describe
the actual post-set Device; the getter then performs its exact cursor handoffs.
All Stops remain outside this normal-return contract. -/
theorem key_mixed_get_after_set (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (key : Key) (sock : NlSock)
    (established : d.staticIdentity.hasIdentity = true)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (readable : ∀ pid ∈ d.peerList, ∀ id ∈ (peers pid).allowedipsList, d.nodes[id]? = some (nodes id))
    (ready : MixedPageReady (keyReadbackBase d key) peers nodes
      (mixedInitialRows (keyReadbackBase d key) peers) {hasWg := true})
    (headerFits : devicePrefixSpace (keyReadbackBase d key) ≤ NLMSG_GOODSIZE)
    (fresh : MixedPlanFresh (keyReadbackBase d key) peers
      (mixedPages (keyReadbackBase d key) peers nodes (mixedInitialRows (keyReadbackBase d key) peers)
        {hasWg := true} ready))
    (cursorData : MixedPlanCursorData (keyReadbackBase d key)
      (mixedPages (keyReadbackBase d key) peers nodes (mixedInitialRows (keyReadbackBase d key) peers)
        {hasWg := true} ready))
    (within : mixedPageReceiveCount
      (mixedPages (keyReadbackBase d key) peers nodes (mixedInitialRows (keyReadbackBase d key) peers)
        {hasWg := true} ready) ≤ 4096)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let pages := mixedPages (keyReadbackBase d key) peers nodes
      (mixedInitialRows (keyReadbackBase d key) peers) {hasWg := true} ready
    Campaign2.Ensures (do
      let ret ← wgSetDevice (privateKeyAttrs d key)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = (0,.ok (mixedGetterJson (keyReadbackBase d key) peers nodes)) ∧
        ∃ postSet observations, ∃ values : PeerId → Peer,
          ObservedKeyPeerRun false (keyReadbackBase d key) d.peerList observations postSet ∧
          (∀ q ∈ d.peerList, postSet.peers[q]? = some (values q)) ∧
          (∀ q, keyGetterPeerView (values q) = keyGetterPeerView (peers q)) ∧
          s.wg.device = some (mixedPagesDevice postSet pages) ∧
          s.wg.nlSock7 = socketReadbackFinal sock postSet ∧
          CursorHeld postSet (mixedPagesDevice postSet pages) none) := by
  dsimp only
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
    have sequence : current.peerAllowedips.seq = (keyReadbackBase d key).peerAllowedips.seq := by
      have h := congrArg (fun base : Device => base.peerAllowedips.seq) fields
      exact h
    have nodesEq : current.nodes = d.nodes := by
      have h := congrArg Device.nodes fields
      exact h
    obtain ⟨rowsEq,json,freshEq,cursorEq⟩ := mixedGetter_data_congr (keyReadbackBase d key) current
      peers values members attrs same lookup nodes
    have translatedReady : MixedPageReady current values nodes
        (mixedInitialRows (keyReadbackBase d key) peers) {hasWg := true} :=
      (mixedPageReady_getter_congr (keyReadbackBase d key) current peers values space same nodes _ _).mpr ready
    have currentReady : MixedPageReady current values nodes (mixedInitialRows current values) {hasWg := true} := by
      simpa only [rowsEq] using translatedReady
    have plan : mixedPages current values nodes (mixedInitialRows current values) {hasWg := true} currentReady =
        mixedPages (keyReadbackBase d key) peers nodes (mixedInitialRows (keyReadbackBase d key) peers)
          {hasWg := true} ready := by
      simpa only [rowsEq] using mixedPages_getter_congr (keyReadbackBase d key) current peers values space
        sequence same nodes _ {hasWg := true} ready translatedReady
    have selection : selectsDevice middle current := by
      have original : selectsDevice entry d := pre.2.2
      simpa [selectsDevice,framed.2,index,name] using original
    obtain ⟨dump,out,rest,getRun,dumped,finalDevice,finalSocket,held⟩ :=
      mixed_getter_returns current values nodes sock currentReady
        (by simpa only [members] using currentResidents)
        (by intro q member id belongs
            rw [nodesEq]
            exact readable q (members ▸ member) id ((details q).2.2.2.1 ▸ belongs))
        (by simpa only [space] using headerFits)
        (by rw [plan]; exact (freshEq _).mpr fresh)
        (by rw [plan]; exact (cursorEq _).mpr cursorData)
        idle emptyQueue (by simpa only [plan] using within)
        middle next ⟨device,framed.1,selection⟩
    have selector : byIndex d = byIndex current := by simp [byIndex,index]
    rw [setRun] at run
    change (((wgGetDevice (byIndex d)).run middle).run next >>= fun ((dump,out),rest) =>
      Except.ok (((ret,dump),out),rest)) = _ at run
    rw [selector,getRun] at run
    cases run
    exact ⟨by simp [code,dumped,json], current,observations,values,effect,
      currentResidents,same,by simpa only [plan] using finalDevice,finalSocket,by simpa only [plan] using held⟩

end Leanux.Proofs.WG.Config
