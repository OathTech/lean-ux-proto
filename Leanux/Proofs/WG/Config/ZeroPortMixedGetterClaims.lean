import Leanux.Proofs.WG.Config.PortMixedGetterFrames
import Leanux.Proofs.WG.Config.MixedGetterInputFrames
import Leanux.Proofs.WG.Config.PeerKeyGetterFrames
import Leanux.Proofs.WG.Config.ZeroPortOutcomeSource
import Leanux.Proofs.WG.Config.ZeroPortOutcomeFrames
import Leanux.Proofs.WG.Config.ZeroPortReadbackFrames
import Leanux.Proofs.WG.Config.MixedGetterClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- On normal return, the actual zero-port request and full mixed getter
expose the actual chosen-port scalar Device and source-clearing effects. Static
pagination premises use only the entry's generation-updated capacity/data; no
successful draw, free-candidate or callback-execution premise is supplied. -/
theorem zero_port_mixed_get_after_set (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (sock : NlSock) (net : d.creatingNet = true)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (readable : ∀ pid ∈ d.peerList, ∀ id ∈ (peers pid).allowedipsList, d.nodes[id]? = some (nodes id))
    (ready : MixedPageReady (requestGeneration d) peers nodes
      (mixedInitialRows (requestGeneration d) peers) {hasWg := true})
    (headerFits : devicePrefixSpace (requestGeneration d) ≤ NLMSG_GOODSIZE)
    (fresh : MixedPlanFresh (requestGeneration d) peers
      (mixedPages (requestGeneration d) peers nodes (mixedInitialRows (requestGeneration d) peers)
        {hasWg := true} ready))
    (cursorData : MixedPlanCursorData (requestGeneration d)
      (mixedPages (requestGeneration d) peers nodes (mixedInitialRows (requestGeneration d) peers)
        {hasWg := true} ready))
    (within : mixedPageReceiveCount
      (mixedPages (requestGeneration d) peers nodes (mixedInitialRows (requestGeneration d) peers)
        {hasWg := true} ready) ≤ 4096)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let pages := mixedPages (requestGeneration d) peers nodes
      (mixedInitialRows (requestGeneration d) peers) {hasWg := true} ready
    Campaign2.Ensures (do
      let ret ← wgSetDevice (portAttrs d 0)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧
        s.wg.nlSock7 = sock)
      (fun result s => ∃ chosen, ZeroPortRequestChoice d chosen ∧
        result = (0,.ok (mixedGetterJson (zeroPortRequestDevice d chosen) peers nodes)) ∧
        ∃ postSet, ∃ values : PeerId → Peer,
          withoutPeers postSet = withoutPeers (zeroPortRequestDevice d chosen) ∧
          (if d.incomingPort = 0 then postSet = requestGeneration d
            else ClearedPeerStore d postSet d.peerList) ∧
          (∀ q ∈ d.peerList, postSet.peers[q]? = some (values q)) ∧
          (∀ q, keyGetterPeerView (values q) = keyGetterPeerView (peers q)) ∧
          s.wg.device = some (mixedPagesDevice postSet pages) ∧
          s.wg.nlSock7 = socketReadbackFinal sock postSet ∧
          CursorHeld postSet (mixedPagesDevice postSet pages) none) := by
  dsimp only
  intro entry ambient result final after pre run
  change (((wgSetDevice (portAttrs d 0)).run entry).run ambient >>= fun ((ret,middle),next) =>
    ((wgGetDevice (byIndex d)).run middle).run next >>= fun ((dump,out),rest) =>
      Except.ok (((ret,dump),out),rest)) = _ at run
  cases setRun : ((wgSetDevice (portAttrs d 0)).run entry).run ambient with
  | error stop => rw [setRun] at run; cases run
  | ok out =>
    obtain ⟨⟨ret,middle⟩,next⟩ := out
    have framed := setDevice_port_zero_configurationFrame d entry.portBound sock entry.fixtureNetDevices
      entry ambient ret middle next ⟨pre.1,pre.2.1,rfl,pre.2.2,rfl⟩ setRun
    obtain ⟨code,chosen,current,choice,device,fields,effect⟩ := setDevice_zeroPort_effect d net
      entry ambient ret middle next ⟨pre.1,pre.2.1⟩ setRun
    have baseFields := zeroPortRequestDevice_frame d chosen
    have basePeers : (zeroPortRequestDevice d chosen).peers = d.peers := by
      have h := congrArg Device.peers baseFields
      exact h
    have lookup : ∀ q : PeerId, (current.peers[q]?).map keyGetterPeerView =
        (d.peers[q]?).map keyGetterPeerView := by
      intro q
      by_cases samePort : d.incomingPort = 0
      · have equal : current = requestGeneration d := by
          simpa only [samePort,ite_true] using effect
        rw [equal]
        rfl
      · exact clearedPeerStore_getter_frame d current d.peerList
          (by simpa only [samePort,ite_false] using effect) q
    let values := keyGetterPeers d current peers
    have baseMembers : (zeroPortRequestDevice d chosen).peerList = d.peerList := by
      have h := congrArg Device.peerList baseFields
      exact h
    obtain ⟨currentResidents,same⟩ := keyGetterPeers_frame d current peers lookup residents
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
      exact h.trans baseMembers
    have space : devicePrefixSpace current = devicePrefixSpace (requestGeneration d) := by
      have h := congrArg devicePrefixSpace fields
      have hbase := congrArg devicePrefixSpace baseFields
      exact h.trans hbase
    have index : current.ifindex = d.ifindex := by
      have h := congrArg Device.ifindex fields
      have original := congrArg Device.ifindex baseFields
      exact h.trans original
    have name : current.ifname = d.ifname := by
      have h := congrArg Device.ifname fields
      have original := congrArg Device.ifname baseFields
      exact h.trans original
    have attrs : deviceFixedAttrs current = deviceFixedAttrs (zeroPortRequestDevice d chosen) :=
      by have h := congrArg deviceFixedAttrs fields; exact h
    have sequence : current.peerAllowedips.seq = (requestGeneration d).peerAllowedips.seq := by
      have h := congrArg (fun base : Device => base.peerAllowedips.seq) fields
      have hbase := congrArg (fun base : Device => base.peerAllowedips.seq) baseFields
      exact h.trans hbase
    have nodesEq : current.nodes = d.nodes := by
      have h := congrArg Device.nodes fields
      have original := congrArg Device.nodes baseFields
      exact h.trans original
    obtain ⟨_rowsChosen,json,freshEq,cursorEq⟩ := mixedGetter_data_congr (zeroPortRequestDevice d chosen) current
      peers values (members.trans baseMembers.symm) attrs same
      (by intro q; rw [basePeers]; exact lookup q) nodes
    have rowsEq : mixedInitialRows current values = mixedInitialRows (requestGeneration d) peers := by
      simp only [mixedInitialRows,members,(details _).2.2.2.1,requestGeneration]
    have chosenFresh : MixedPlanFresh (zeroPortRequestDevice d chosen) peers
        (mixedPages (requestGeneration d) peers nodes (mixedInitialRows (requestGeneration d) peers)
          {hasWg := true} ready) := by
      have original : MixedPlanFresh d peers
          (mixedPages (requestGeneration d) peers nodes (mixedInitialRows (requestGeneration d) peers)
            {hasWg := true} ready) := fresh
      simpa only [MixedPlanFresh,MixedBoundaryFresh,baseMembers] using original
    have chosenCursorData : MixedPlanCursorData (zeroPortRequestDevice d chosen)
        (mixedPages (requestGeneration d) peers nodes (mixedInitialRows (requestGeneration d) peers)
          {hasWg := true} ready) := by
      have original : MixedPlanCursorData d
          (mixedPages (requestGeneration d) peers nodes (mixedInitialRows (requestGeneration d) peers)
            {hasWg := true} ready) := cursorData
      simpa only [MixedPlanCursorData,basePeers] using original
    have translatedReady : MixedPageReady current values nodes
        (mixedInitialRows (requestGeneration d) peers) {hasWg := true} :=
      (mixedPageReady_getter_congr (requestGeneration d) current peers values space same nodes _ _).mpr ready
    have currentReady : MixedPageReady current values nodes (mixedInitialRows current values) {hasWg := true} := by
      simpa only [rowsEq] using translatedReady
    have plan : mixedPages current values nodes (mixedInitialRows current values) {hasWg := true} currentReady =
        mixedPages (requestGeneration d) peers nodes (mixedInitialRows (requestGeneration d) peers)
          {hasWg := true} ready := by
      simpa only [rowsEq] using mixedPages_getter_congr (requestGeneration d) current peers values space
        sequence same nodes _ {hasWg := true} ready translatedReady
    have selection : selectsDevice middle current := by
      have original : selectsDevice entry d := pre.2.1
      simpa [selectsDevice,framed.2.2,index,name] using original
    obtain ⟨dump,out,rest,getRun,dumped,finalDevice,finalSocket,held⟩ :=
      mixed_getter_returns current values nodes sock currentReady
        (by simpa only [members] using currentResidents)
        (by intro q member id belongs
            rw [nodesEq]
            exact readable q (members ▸ member) id ((details q).2.2.2.1 ▸ belongs))
        (by simpa only [space] using headerFits)
        (by rw [plan]; exact (freshEq _).mpr chosenFresh)
        (by rw [plan]; exact (cursorEq _).mpr chosenCursorData)
        idle emptyQueue (by simpa only [plan] using within)
        middle next ⟨device,framed.2.1,selection⟩
    have selector : byIndex d = byIndex current := by simp [byIndex,index]
    rw [setRun] at run
    change (((wgGetDevice (byIndex d)).run middle).run next >>= fun ((dump,out),rest) =>
      Except.ok (((ret,dump),out),rest)) = _ at run
    rw [selector,getRun] at run
    cases run
    exact ⟨chosen,choice,by simp [code,dumped,json], current,values,fields,effect,
      currentResidents,same,by simpa only [plan] using finalDevice,finalSocket,by simpa only [plan] using held⟩

end Leanux.Proofs.WG.Config
