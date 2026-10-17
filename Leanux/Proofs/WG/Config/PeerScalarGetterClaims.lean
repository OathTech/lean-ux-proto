import Leanux.Proofs.WG.Config.MultiPeerScalarEffects
import Leanux.Proofs.WG.Config.PeerGetterClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Actual existing-peer scalar setter followed by the finite empty-IP peer
getter. A malformed second peer returns -EINVAL after the first peer's PSK and
keepalive writes. JSON reflects the update at every listed occurrence;
an unlisted target changes only the Device. Pagination conditions concern
the effective successor, with freshness and lifetime data restricted to
computed nonfinal cursors. Every getter callback and receive is derived. -/
theorem scalar_paginated_peers_get_after_set (d : Device) (peers : PeerId → Peer)
    (key psk : Key) (interval : Nat) (bad : Bool) (pid : PeerId) (sock : NlSock)
    (found : d.peerHashtable.find? (·.1 == key) = some (key,pid))
    (resident : d.peers[pid]? = some (peers pid))
    (live : 0 < (peers pid).refcount) (bounded : (peers pid).refcount + 1 < 2 ^ 31)
    (down : d.running = false)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (emptyIps : ∀ q ∈ d.peerList, (peers q).allowedipsList = [])
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let updated := scalarRequestDevice d pid (peers pid) psk interval
    let configured := scalarPeerView peers pid psk interval
    devicePrefixSpace updated ≤ NLMSG_GOODSIZE →
    (∀ q rest, updated.peerList = q :: rest →
      peerFixedSpace (configured q) ≤ NLMSG_GOODSIZE-devicePrefixSpace updated) →
    peerPageBoundaryFresh [] (peerPages configured updated updated.peerList) →
    PeerPageCursorData configured (peerPages configured updated updated.peerList) →
    peerPageReceiveCount configured updated updated.peerList ≤ 4096 →
    Campaign2.Returns (do
      let ret ← wgSetDevice (scalarDeviceAttrs d key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        result = ((if bad then -EINVAL else 0),.ok (multiPeerJson updated configured)) ∧
        s.wg.device = some (peerGetterFinalDevice updated configured) ∧
        s.wg.nlSock7 = socketReadbackFinal sock updated ∧
        CursorHeld updated (peerGetterFinalDevice updated configured) none) := by
  dsimp only
  intro headerFits firstFits fresh cursorData within
  intro initial ambient pre
  obtain ⟨device,socket,selected⟩ := pre
  obtain ⟨ret,afterSet,setAmbient,setRun,retEq,setDevice,framed⟩ :=
    setDevice_scalars_framed d key psk interval bad pid (peers pid) sock initial.fixtureNetDevices
      found resident live bounded down initial ambient ⟨device,⟨socket,rfl⟩,selected⟩
  let updated := scalarRequestDevice d pid (peers pid) psk interval
  let configured := scalarPeerView peers pid psk interval
  obtain ⟨_,sameName,sameIndex,_,currentResidents,currentEmpty⟩ :=
    scalarRequestDevice_dump_effect d peers pid psk interval residents emptyIps
  have selection : selectsDevice afterSet updated := by
    change selectsDevice initial d at selected
    simpa only [selectsDevice,updated,sameName,sameIndex,framed.2] using selected
  obtain ⟨dump,final,after,getRun,dumpEq,finalDevice,finalSocket,finalHeld⟩ :=
    peer_getter_returns updated configured sock currentResidents currentEmpty headerFits
      firstFits fresh cursorData idle emptyQueue within afterSet setAmbient ⟨setDevice,framed.1,selection⟩
  refine ⟨(ret,dump),final,after,?_,?_,finalDevice,finalSocket,finalHeld⟩
  · change (((wgSetDevice (scalarDeviceAttrs d key psk interval bad)).run initial).run ambient >>= _) = _
    rw [setRun]
    change (((wgGetDevice (byIndex d)).run afterSet).run setAmbient >>= _) = _
    have selector : byIndex d = byIndex updated := by
      simp only [byIndex,updated,sameIndex]
    rw [selector,getRun]
    rfl
  · simp [retEq,dumpEq,updated,configured]

end Leanux.Proofs.WG.Config
