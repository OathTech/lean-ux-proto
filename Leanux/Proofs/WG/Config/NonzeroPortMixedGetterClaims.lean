import Leanux.Proofs.WG.Config.PortMixedGetterFrames
import Leanux.Proofs.WG.Config.MixedGetterInputFrames
import Leanux.Proofs.WG.Config.PeerKeyGetterFrames
import Leanux.Proofs.WG.Config.PortOutcomeSource
import Leanux.Proofs.WG.Config.PortOutcomeFrames
import Leanux.Proofs.WG.Config.PortReadbackFrames
import Leanux.Proofs.WG.Config.MixedGetterClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- On normal return, the original nonzero port-only request followed by the
full finite mixed getter exposes the actual same-port, stopped-device, available
bind or refused-bind outcome. Changed-port source clearing and the getter's
ordered cursor handoffs remain explicit; hidden reset Stops are retained. -/
theorem nonzero_port_mixed_get_after_set (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (port : Nat) (bound : Nat → Bool) (sock : NlSock)
    (nonzero : port ≠ 0) (net : d.creatingNet = true)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (readable : ∀ pid ∈ d.peerList, ∀ id ∈ (peers pid).allowedipsList, d.nodes[id]? = some (nodes id))
    (ready : MixedPageReady ((nonzeroPortRequestOutcome d port bound).2) peers nodes
      (mixedInitialRows ((nonzeroPortRequestOutcome d port bound).2) peers) {hasWg := true})
    (headerFits : devicePrefixSpace ((nonzeroPortRequestOutcome d port bound).2) ≤ NLMSG_GOODSIZE)
    (fresh : MixedPlanFresh ((nonzeroPortRequestOutcome d port bound).2) peers
      (mixedPages ((nonzeroPortRequestOutcome d port bound).2) peers nodes (mixedInitialRows ((nonzeroPortRequestOutcome d port bound).2) peers)
        {hasWg := true} ready))
    (cursorData : MixedPlanCursorData ((nonzeroPortRequestOutcome d port bound).2)
      (mixedPages ((nonzeroPortRequestOutcome d port bound).2) peers nodes (mixedInitialRows ((nonzeroPortRequestOutcome d port bound).2) peers)
        {hasWg := true} ready))
    (within : mixedPageReceiveCount
      (mixedPages ((nonzeroPortRequestOutcome d port bound).2) peers nodes (mixedInitialRows ((nonzeroPortRequestOutcome d port bound).2) peers)
        {hasWg := true} ready) ≤ 4096)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let pages := mixedPages ((nonzeroPortRequestOutcome d port bound).2) peers nodes
      (mixedInitialRows ((nonzeroPortRequestOutcome d port bound).2) peers) {hasWg := true} ready
    Campaign2.Ensures (do
      let ret ← wgSetDevice (portAttrs d port)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧
        s.wg.portBound = bound ∧ s.wg.nlSock7 = sock)
      (fun result s => result = ((nonzeroPortRequestOutcome d port bound).1,.ok (mixedGetterJson ((nonzeroPortRequestOutcome d port bound).2) peers nodes)) ∧
        ∃ postSet, ∃ values : PeerId → Peer,
          withoutPeers postSet = withoutPeers ((nonzeroPortRequestOutcome d port bound).2) ∧
          (if d.incomingPort = port then postSet = requestGeneration d
            else ClearedPeerStore d postSet d.peerList) ∧
          (∀ q ∈ d.peerList, postSet.peers[q]? = some (values q)) ∧
          (∀ q, keyGetterPeerView (values q) = keyGetterPeerView (peers q)) ∧
          s.wg.device = some (mixedPagesDevice postSet pages) ∧
          s.wg.nlSock7 = socketReadbackFinal sock postSet ∧
          CursorHeld postSet (mixedPagesDevice postSet pages) none) := by
  dsimp only
  intro entry ambient result final after pre run
  change (((wgSetDevice (portAttrs d port)).run entry).run ambient >>= fun ((ret,middle),next) =>
    ((wgGetDevice (byIndex d)).run middle).run next >>= fun ((dump,out),rest) =>
      Except.ok (((ret,dump),out),rest)) = _ at run
  cases setRun : ((wgSetDevice (portAttrs d port)).run entry).run ambient with
  | error stop => rw [setRun] at run; cases run
  | ok out =>
    obtain ⟨⟨ret,middle⟩,next⟩ := out
    have framed := setDevice_port_nonzero_configurationFrame d port nonzero bound sock entry.fixtureNetDevices
      entry ambient ret middle next ⟨pre.1,pre.2.1,pre.2.2.1,pre.2.2.2,rfl⟩ setRun
    obtain ⟨code,current,device,fields,effect⟩ := setDevice_nonzeroPort_effect d port bound nonzero net
      entry ambient ret middle next ⟨pre.1,pre.2.1,pre.2.2.1⟩ setRun
    have baseFields := nonzeroPortRequestOutcome_frame d port bound
    have basePeers : (nonzeroPortRequestOutcome d port bound).2.peers = d.peers := by
      have h := congrArg Device.peers baseFields
      exact h
    have lookup : ∀ q : PeerId, (current.peers[q]?).map keyGetterPeerView =
        ((nonzeroPortRequestOutcome d port bound).2.peers[q]?).map keyGetterPeerView := by
      intro q
      rw [basePeers]
      by_cases samePort : d.incomingPort = port
      · have equal : current = requestGeneration d := by
          simpa only [samePort,ite_true] using effect
        rw [equal]
        rfl
      · exact clearedPeerStore_getter_frame d current d.peerList
          (by simpa only [samePort,ite_false] using effect) q
    let values := keyGetterPeers ((nonzeroPortRequestOutcome d port bound).2) current peers
    have baseMembers : (nonzeroPortRequestOutcome d port bound).2.peerList = d.peerList := by
      have h := congrArg Device.peerList baseFields
      exact h
    have baseResidents : ∀ q ∈ ((nonzeroPortRequestOutcome d port bound).2).peerList,
        ((nonzeroPortRequestOutcome d port bound).2).peers[q]? = some (peers q) := by
      simpa only [baseMembers,basePeers] using residents
    obtain ⟨currentResidents,same⟩ := keyGetterPeers_frame _ current peers lookup baseResidents
    have currentResidents' : ∀ q ∈ d.peerList, current.peers[q]? = some (values q) := by
      simpa only [baseMembers] using currentResidents
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
      exact h.trans baseMembers
    have space : devicePrefixSpace current = devicePrefixSpace ((nonzeroPortRequestOutcome d port bound).2) :=
      by have h := congrArg devicePrefixSpace fields; exact h
    have index : current.ifindex = d.ifindex := by
      have h := congrArg Device.ifindex fields
      have original := congrArg Device.ifindex baseFields
      exact h.trans original
    have name : current.ifname = d.ifname := by
      have h := congrArg Device.ifname fields
      have original := congrArg Device.ifname baseFields
      exact h.trans original
    have attrs : deviceFixedAttrs current = deviceFixedAttrs ((nonzeroPortRequestOutcome d port bound).2) :=
      by have h := congrArg deviceFixedAttrs fields; exact h
    have sequence : current.peerAllowedips.seq = ((nonzeroPortRequestOutcome d port bound).2).peerAllowedips.seq := by
      have h := congrArg (fun base : Device => base.peerAllowedips.seq) fields
      exact h
    have nodesEq : current.nodes = d.nodes := by
      have h := congrArg Device.nodes fields
      have original := congrArg Device.nodes baseFields
      exact h.trans original
    obtain ⟨rowsEq,json,freshEq,cursorEq⟩ := mixedGetter_data_congr ((nonzeroPortRequestOutcome d port bound).2) current
      peers values (members.trans baseMembers.symm) attrs same lookup nodes
    have translatedReady : MixedPageReady current values nodes
        (mixedInitialRows ((nonzeroPortRequestOutcome d port bound).2) peers) {hasWg := true} :=
      (mixedPageReady_getter_congr ((nonzeroPortRequestOutcome d port bound).2) current peers values space same nodes _ _).mpr ready
    have currentReady : MixedPageReady current values nodes (mixedInitialRows current values) {hasWg := true} := by
      simpa only [rowsEq] using translatedReady
    have plan : mixedPages current values nodes (mixedInitialRows current values) {hasWg := true} currentReady =
        mixedPages ((nonzeroPortRequestOutcome d port bound).2) peers nodes (mixedInitialRows ((nonzeroPortRequestOutcome d port bound).2) peers)
          {hasWg := true} ready := by
      simpa only [rowsEq] using mixedPages_getter_congr ((nonzeroPortRequestOutcome d port bound).2) current peers values space
        sequence same nodes _ {hasWg := true} ready translatedReady
    have selection : selectsDevice middle current := by
      have original : selectsDevice entry d := pre.2.1
      simpa [selectsDevice,framed.2.2,index,name] using original
    obtain ⟨dump,out,rest,getRun,dumped,finalDevice,finalSocket,held⟩ :=
      mixed_getter_returns current values nodes sock currentReady
        (by simpa only [members] using currentResidents')
        (by intro q member id belongs
            rw [nodesEq]
            exact readable q (members ▸ member) id ((details q).2.2.2.1 ▸ belongs))
        (by simpa only [space] using headerFits)
        (by rw [plan]; exact (freshEq _).mpr fresh)
        (by rw [plan]; exact (cursorEq _).mpr cursorData)
        idle emptyQueue (by simpa only [plan] using within)
        middle next ⟨device,framed.2.1,selection⟩
    have selector : byIndex d = byIndex current := by simp [byIndex,index]
    rw [setRun] at run
    change (((wgGetDevice (byIndex d)).run middle).run next >>= fun ((dump,out),rest) =>
      Except.ok (((ret,dump),out),rest)) = _ at run
    rw [selector,getRun] at run
    cases run
    exact ⟨by simp [code,dumped,json], current,values,fields,effect,
      currentResidents',same,by simpa only [plan] using finalDevice,finalSocket,by simpa only [plan] using held⟩

end Leanux.Proofs.WG.Config
