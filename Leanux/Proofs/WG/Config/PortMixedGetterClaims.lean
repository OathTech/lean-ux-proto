import Leanux.Proofs.WG.Config.PortMixedGetterFrames
import Leanux.Proofs.WG.Config.MixedGetterInputFrames
import Leanux.Proofs.WG.Config.PeerKeyGetterFrames
import Leanux.Proofs.WG.Config.PortRefusalSource
import Leanux.Proofs.WG.Config.MixedGetterClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- On normal return, a mixed request refused at its changed nonzero port
exposes its committed mark/generation and ordered source-clearing effects through
the actual full mixed getter. Later supported attributes are bypassed; hidden
reset Stops are retained. The getter performs its real cursor handoffs. -/
theorem port_refusal_mixed_get_after_set (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (mark port : Nat) (flags : Option UInt32)
    (key : Option Key) (entries : Option (List PeerEntry)) (bound : Nat → Bool) (sock : NlSock)
    (supported : flags.getD 0 &&& ~~~WGDEVICE_F_ALL = 0)
    (net : d.creatingNet = true) (running : d.running = true)
    (nonzero : port ≠ 0) (changed : d.incomingPort ≠ port)
    (collision : (bound port || d.sock4 == some port || d.sock6 == some port) = true)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (readable : ∀ pid ∈ d.peerList, ∀ id ∈ (peers pid).allowedipsList, d.nodes[id]? = some (nodes id))
    (ready : MixedPageReady (portRefusalBase d mark) peers nodes
      (mixedInitialRows (portRefusalBase d mark) peers) {hasWg := true})
    (headerFits : devicePrefixSpace (portRefusalBase d mark) ≤ NLMSG_GOODSIZE)
    (fresh : MixedPlanFresh (portRefusalBase d mark) peers
      (mixedPages (portRefusalBase d mark) peers nodes (mixedInitialRows (portRefusalBase d mark) peers)
        {hasWg := true} ready))
    (cursorData : MixedPlanCursorData (portRefusalBase d mark)
      (mixedPages (portRefusalBase d mark) peers nodes (mixedInitialRows (portRefusalBase d mark) peers)
        {hasWg := true} ready))
    (within : mixedPageReceiveCount
      (mixedPages (portRefusalBase d mark) peers nodes (mixedInitialRows (portRefusalBase d mark) peers)
        {hasWg := true} ready) ≤ 4096)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let pages := mixedPages (portRefusalBase d mark) peers nodes
      (mixedInitialRows (portRefusalBase d mark) peers) {hasWg := true} ready
    Campaign2.Ensures (do
      let ret ← wgSetDevice (portRefusalAttrs d mark port flags key entries)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧
        s.wg.portBound = bound ∧ s.wg.nlSock7 = sock)
      (fun result s => result = (-EADDRINUSE,.ok (mixedGetterJson (portRefusalBase d mark) peers nodes)) ∧
        ∃ postSet, ∃ values : PeerId → Peer,
          withoutPeers postSet = withoutPeers (portRefusalBase d mark) ∧
          ClearedPeerStore d postSet d.peerList ∧
          (∀ q ∈ d.peerList, postSet.peers[q]? = some (values q)) ∧
          (∀ q, keyGetterPeerView (values q) = keyGetterPeerView (peers q)) ∧
          s.wg.device = some (mixedPagesDevice postSet pages) ∧
          s.wg.nlSock7 = socketReadbackFinal sock postSet ∧
          CursorHeld postSet (mixedPagesDevice postSet pages) none) := by
  dsimp only
  intro entry ambient result final after pre run
  change (((wgSetDevice (portRefusalAttrs d mark port flags key entries)).run entry).run ambient >>= fun ((ret,middle),next) =>
    ((wgGetDevice (byIndex d)).run middle).run next >>= fun ((dump,out),rest) =>
      Except.ok (((ret,dump),out),rest)) = _ at run
  cases setRun : ((wgSetDevice (portRefusalAttrs d mark port flags key entries)).run entry).run ambient with
  | error stop => rw [setRun] at run; cases run
  | ok out =>
    obtain ⟨⟨ret,middle⟩,next⟩ := out
    obtain ⟨code,framed,outer,clears⟩ := setDevice_mixed_port_refused d mark port flags key entries
      bound sock entry.fixtureNetDevices supported net running nonzero changed collision
      entry ambient ret middle next ⟨pre.1,pre.2.1,pre.2.2.1,pre.2.2.2,rfl⟩ setRun
    obtain ⟨current,device,fields⟩ := Option.map_eq_some_iff.mp outer
    have effect : ClearedPeerStore d current d.peerList := by
      simpa only [clearedPeers,device,Option.bind_some,ClearedPeerStore] using clears
    have lookup : ∀ q : PeerId, (current.peers[q]?).map keyGetterPeerView =
        ((portRefusalBase d mark).peers[q]?).map keyGetterPeerView :=
      clearedPeerStore_getter_frame d current d.peerList effect
    let values := keyGetterPeers (portRefusalBase d mark) current peers
    have baseResidents : ∀ q ∈ (portRefusalBase d mark).peerList,
        (portRefusalBase d mark).peers[q]? = some (peers q) := residents
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
    have space : devicePrefixSpace current = devicePrefixSpace (portRefusalBase d mark) :=
      by have h := congrArg devicePrefixSpace fields; exact h
    have index : current.ifindex = d.ifindex := by
      have h := congrArg Device.ifindex fields
      exact h
    have name : current.ifname = d.ifname := by
      have h := congrArg Device.ifname fields
      exact h
    have attrs : deviceFixedAttrs current = deviceFixedAttrs (portRefusalBase d mark) :=
      by have h := congrArg deviceFixedAttrs fields; exact h
    have sequence : current.peerAllowedips.seq = (portRefusalBase d mark).peerAllowedips.seq := by
      have h := congrArg (fun base : Device => base.peerAllowedips.seq) fields
      exact h
    have nodesEq : current.nodes = d.nodes := by
      have h := congrArg Device.nodes fields
      exact h
    obtain ⟨rowsEq,json,freshEq,cursorEq⟩ := mixedGetter_data_congr (portRefusalBase d mark) current
      peers values members attrs same lookup nodes
    have translatedReady : MixedPageReady current values nodes
        (mixedInitialRows (portRefusalBase d mark) peers) {hasWg := true} :=
      (mixedPageReady_getter_congr (portRefusalBase d mark) current peers values space same nodes _ _).mpr ready
    have currentReady : MixedPageReady current values nodes (mixedInitialRows current values) {hasWg := true} := by
      simpa only [rowsEq] using translatedReady
    have plan : mixedPages current values nodes (mixedInitialRows current values) {hasWg := true} currentReady =
        mixedPages (portRefusalBase d mark) peers nodes (mixedInitialRows (portRefusalBase d mark) peers)
          {hasWg := true} ready := by
      simpa only [rowsEq] using mixedPages_getter_congr (portRefusalBase d mark) current peers values space
        sequence same nodes _ {hasWg := true} ready translatedReady
    have selection : selectsDevice middle current := by
      have original : selectsDevice entry d := pre.2.1
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
    exact ⟨by simp [code,dumped,json], current,values,fields,effect,
      currentResidents,same,by simpa only [plan] using finalDevice,finalSocket,by simpa only [plan] using held⟩

end Leanux.Proofs.WG.Config
