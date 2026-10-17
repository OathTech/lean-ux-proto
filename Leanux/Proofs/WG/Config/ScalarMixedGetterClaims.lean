import Leanux.Proofs.WG.Config.ScalarMixedGetterEffects
import Leanux.Proofs.WG.Config.MixedGetterClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Actual existing-peer PSK/keepalive configuration followed by the full finite
mixed peer/allowed-IP getter. A malformed second peer retains the first peer's
writes and returns -EINVAL; the getter then reads that actual updated Device.
Duplicates, arbitrary endpoints and node widths retain their original order.
Only computed boundary freshness, cursor references and page-budget conditions
are imposed on the pure successor; every native callback is derived. -/
theorem scalar_mixed_get_after_set (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (key psk : Key) (interval : Nat) (bad : Bool)
    (pid : PeerId) (sock : NlSock)
    (found : d.peerHashtable.find? (·.1 == key) = some (key,pid))
    (resident : d.peers[pid]? = some (peers pid))
    (live : 0 < (peers pid).refcount) (bounded : (peers pid).refcount+1 < 2^31)
    (down : d.running = false)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (readable : ∀ q ∈ d.peerList, ∀ id ∈ (peers q).allowedipsList, d.nodes[id]? = some (nodes id))
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let updated := scalarRequestDevice d pid (peers pid) psk interval
    let configured := scalarPeerView peers pid psk interval
    ∀ ready : MixedPageReady updated configured nodes (mixedInitialRows updated configured) {hasWg := true},
    devicePrefixSpace updated ≤ NLMSG_GOODSIZE →
    MixedPlanFresh updated configured
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) →
    MixedPlanCursorData updated
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) →
    mixedPageReceiveCount
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) ≤ 4096 →
    Campaign2.Returns (do
      let ret ← wgSetDevice (scalarDeviceAttrs d key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        let pages := mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready
        result = ((if bad then -EINVAL else 0),.ok (mixedGetterJson updated configured nodes)) ∧
        s.wg.device = some (mixedPagesDevice updated pages) ∧
        s.wg.nlSock7 = socketReadbackFinal sock updated ∧
        CursorHeld updated (mixedPagesDevice updated pages) none) := by
  dsimp only
  intro ready headerFits fresh cursorData within
  intro initial ambient pre
  obtain ⟨device,socket,selected⟩ := pre
  obtain ⟨ret,afterSet,setAmbient,setRun,retEq,setDevice,framed⟩ :=
    setDevice_scalars_framed d key psk interval bad pid (peers pid) sock initial.fixtureNetDevices
      found resident live bounded down initial ambient ⟨device,⟨socket,rfl⟩,selected⟩
  let updated := scalarRequestDevice d pid (peers pid) psk interval
  let configured := scalarPeerView peers pid psk interval
  obtain ⟨sameList,sameName,sameIndex,sameNodes,currentResidents,sameIps⟩ :=
    scalarRequestDevice_mixed_effect d peers pid psk interval residents
  have currentReadable : ∀ q ∈ updated.peerList, ∀ id ∈ (configured q).allowedipsList,
      updated.nodes[id]? = some (nodes id) := by
    intro q member id node
    rw [sameList] at member
    rw [sameIps] at node
    rw [sameNodes]
    exact readable q member id node
  have selection : selectsDevice afterSet updated := by
    change selectsDevice initial d at selected
    simpa only [selectsDevice,updated,sameName,sameIndex,framed.2] using selected
  obtain ⟨dump,final,after,getRun,dumpEq,finalDevice,finalSocket,finalHeld⟩ :=
    mixed_getter_returns updated configured nodes sock ready currentResidents currentReadable headerFits
      fresh cursorData idle emptyQueue within afterSet setAmbient ⟨setDevice,framed.1,selection⟩
  refine ⟨(ret,dump),final,after,?_,?_,finalDevice,finalSocket,finalHeld⟩
  · change (((wgSetDevice (scalarDeviceAttrs d key psk interval bad)).run initial).run ambient >>= _) = _
    rw [setRun]
    change (((wgGetDevice (byIndex d)).run afterSet).run setAmbient >>= _) = _
    have selector : byIndex d = byIndex updated := by simp only [byIndex,updated,sameIndex]
    rw [selector,getRun]
    rfl
  · simp [retEq,dumpEq,updated,configured]

end Leanux.Proofs.WG.Config
