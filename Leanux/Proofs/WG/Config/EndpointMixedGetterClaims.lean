import Leanux.Proofs.WG.Config.EndpointRequestSource
import Leanux.Proofs.WG.Config.EndpointGetterFrames
import Leanux.Proofs.WG.Config.MixedGetterInputFrames
import Leanux.Proofs.WG.Config.MixedGetterClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Actual endpoint configuration followed by the complete finite mixed getter.
Static page premises use the pure successor with no reset timestamp; any actual
reset preserves those inputs. Earlier writes before later EINVAL, ignored endpoint
encodings, equality-retained fields and record-driven Stops remain unchanged. -/
theorem endpoint_mixed_get_after_set (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (key : Key) (a : EndpointAttr)
    (updateOnly bad : Bool) (pid : PeerId) (sock : NlSock)
    (found : d.peerHashtable.find? (·.1 == key) = some (key,pid))
    (resident : d.peers[pid]? = some (peers pid))
    (live : 0 < (peers pid).refcount) (bounded : (peers pid).refcount+1 < 2^31)
    (down : d.running = false)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (readable : ∀ q ∈ d.peerList, ∀ id ∈ (peers q).allowedipsList, d.nodes[id]? = some (nodes id))
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let base := {d with deviceUpdateGen := d.deviceUpdateGen+1}
    let updated := endpointSetterDevice base pid (peers pid) a none
    let configured := fun q => if q = pid then endpointAttributePeer (peers q) a none else peers q
    ∀ ready : MixedPageReady updated configured nodes (mixedInitialRows updated configured) {hasWg := true},
    devicePrefixSpace updated ≤ NLMSG_GOODSIZE →
    MixedPlanFresh updated configured
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) →
    MixedPlanCursorData updated
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) →
    mixedPageReceiveCount
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) ≤ 4096 →
    Campaign2.Ensures (do
      let ret ← wgSetDevice (endpointDeviceAttrs d key a updateOnly bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        let pages := mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready
        result = ((if bad then -EINVAL else 0),.ok (mixedGetterJson updated configured nodes)) ∧
        ∃ reset, let postSet := endpointSetterDevice base pid (peers pid) a reset
          s.wg.device = some (mixedPagesDevice postSet pages) ∧
          s.wg.nlSock7 = socketReadbackFinal sock postSet ∧
          CursorHeld postSet (mixedPagesDevice postSet pages) none) := by
  dsimp only
  intro ready headerFits fresh cursorData within
  intro entry ambient result final after pre run
  change (((wgSetDevice (endpointDeviceAttrs d key a updateOnly bad)).run entry).run ambient >>=
    fun ((ret,middle),next) => ((wgGetDevice (byIndex d)).run middle).run next >>=
      fun ((dump,out),rest) => Except.ok (((ret,dump),out),rest)) = _ at run
  cases setRun : ((wgSetDevice (endpointDeviceAttrs d key a updateOnly bad)).run entry).run ambient with
  | error stop => rw [setRun] at run; cases run
  | ok output =>
    obtain ⟨⟨ret,middle⟩,next⟩ := output
    obtain ⟨code,reset,device,framed⟩ := setDevice_endpoint d key a updateOnly bad pid (peers pid) sock
      entry.fixtureNetDevices found resident live bounded down entry ambient ret middle next
      ⟨pre.1,⟨pre.2.1,rfl⟩,pre.2.2⟩ setRun
    let base := {d with deviceUpdateGen := d.deviceUpdateGen+1}
    let updated := endpointSetterDevice base pid (peers pid) a none
    let configured := fun q => if q = pid then endpointAttributePeer (peers q) a none else peers q
    let current := endpointSetterDevice base pid (peers pid) a reset
    let values := fun q => if q = pid then endpointAttributePeer (peers q) a reset else peers q
    have fields := endpointSetter_fields base pid (peers pid) a reset
    have retained := endpointSetter_getter_frame base pid (peers pid) a reset
    have members : current.peerList = updated.peerList := by
      have h := congrArg Device.peerList retained.1
      exact h
    have oldMembers : current.peerList = d.peerList := by
      have h := congrArg Device.peerList fields.1
      exact h
    have space : devicePrefixSpace current = devicePrefixSpace updated := by
      have h := congrArg devicePrefixSpace retained.1
      exact h
    have sequence : current.peerAllowedips.seq = updated.peerAllowedips.seq :=
      by
        have h := congrArg (fun t : Device => t.peerAllowedips.seq) retained.1
        exact h
    have attrs : deviceFixedAttrs current = deviceFixedAttrs updated := by
      have h := congrArg deviceFixedAttrs retained.1
      exact h
    have index : current.ifindex = d.ifindex := by
      have h := congrArg Device.ifindex fields.1
      exact h
    have name : current.ifname = d.ifname := by
      have h := congrArg Device.ifname fields.1
      exact h
    have nodeMap : current.nodes = d.nodes := by
      have h := congrArg Device.nodes fields.1
      exact h
    have same (q : PeerId) : keyGetterPeerView (values q) = keyGetterPeerView (configured q) := by
      by_cases equal : q = pid
      · simpa only [values,configured,ite_eq_left equal] using
          (endpointAttributePeer_getter_frame (peers q) a reset).trans
            (endpointAttributePeer_getter_frame (peers q) a none).symm
      · simp only [values,configured,ite_eq_right equal]
    have currentResidents : ∀ q ∈ current.peerList, current.peers[q]? = some (values q) := by
      intro q member
      by_cases equal : q = pid
      · subst q
        simpa only [values,ite_true] using fields.2.1
      · simpa only [current,endpointSetter_other base pid q (peers pid) a reset equal,
          values,ite_eq_right equal] using residents q (oldMembers ▸ member)
    have currentReadable : ∀ q ∈ current.peerList, ∀ id ∈ (values q).allowedipsList,
        current.nodes[id]? = some (nodes id) := by
      intro q member id node
      have ips : (values q).allowedipsList = (peers q).allowedipsList := by
        by_cases equal : q = pid
        · simpa only [values,ite_eq_left equal] using
            (endpointSetter_fields base q (peers q) a reset).2.2.1
        · simp only [values,ite_eq_right equal]
      rw [ips] at node
      rw [nodeMap]
      exact readable q (oldMembers ▸ member) id node
    obtain ⟨rows,json,freshness,lifetime⟩ :=
      mixedGetter_data_congr updated current configured values members attrs same retained.2 nodes
    have currentReady : MixedPageReady current values nodes (mixedInitialRows current values) {hasWg := true} := by
      rw [rows]
      exact (mixedPageReady_getter_congr updated current configured values space same nodes _ _).mpr ready
    have plan : mixedPages current values nodes (mixedInitialRows current values) {hasWg := true} currentReady =
        mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready := by
      have bridge := mixedPages_getter_congr updated current configured values space sequence same
        nodes (mixedInitialRows updated configured) {hasWg := true} ready
        ((mixedPageReady_getter_congr updated current configured values space same nodes _ _).mpr ready)
      simpa only [rows] using bridge
    have selection : selectsDevice middle current := by
      have selected : selectsDevice entry d := pre.2.2
      simpa only [selectsDevice,index,name,framed.2] using selected
    obtain ⟨dump,out,rest,getRun,dumped,finalDevice,finalSocket,held⟩ :=
      mixed_getter_returns current values nodes sock currentReady currentResidents currentReadable
        (by simpa only [space] using headerFits)
        (by rw [plan]; exact (freshness _).mpr fresh)
        (by rw [plan]; exact (lifetime _).mpr cursorData)
        idle emptyQueue (by simpa only [plan] using within)
        middle next ⟨device,framed.1,selection⟩
    have selector : byIndex d = byIndex current := by simp only [byIndex,index]
    rw [setRun] at run
    change (((wgGetDevice (byIndex d)).run middle).run next >>=
      fun ((dump,out),rest) => Except.ok (((ret,dump),out),rest)) = _ at run
    rw [selector,getRun] at run
    cases run
    refine ⟨?_,reset,?_,finalSocket,?_⟩
    · rw [code,dumped,json]
    · simpa only [plan] using finalDevice
    · simpa only [plan] using held

end Leanux.Proofs.WG.Config
