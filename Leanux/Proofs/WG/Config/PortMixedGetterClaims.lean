import Leanux.Proofs.WG.Config.MixedGetterFieldClaims
import Leanux.Proofs.WG.Config.PortRefusalSource

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

    obtain ⟨dump,out,rest,getRun,dumped,values,currentResidents,same,finalDevice,finalSocket,held⟩ :=
      mixed_getter_fields_returns (portRefusalBase d mark) current peers nodes sock fields lookup
        residents readable ready headerFits fresh cursorData within idle emptyQueue
        middle next ⟨device,framed.1,by
          change selectsDevice middle (portRefusalBase d mark)
          have original : selectsDevice entry d := pre.2.1
          simpa [selectsDevice,framed.2,portRefusalBase] using original⟩
    change (∀ q ∈ d.peerList,current.peers[q]? = some (values q)) at currentResidents
    have selector : byIndex d = byIndex (portRefusalBase d mark) := rfl
    rw [setRun] at run
    change (((wgGetDevice (byIndex d)).run middle).run next >>= fun ((dump,out),rest) =>
      Except.ok (((ret,dump),out),rest)) = _ at run
    rw [selector,getRun] at run
    cases run
    exact ⟨by simp [code,dumped],current,values,fields,effect,currentResidents,same,
      finalDevice,finalSocket,held⟩

end Leanux.Proofs.WG.Config
