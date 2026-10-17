import Leanux.Proofs.WG.Config.FwmarkMixedGetterFrames
import Leanux.Proofs.WG.Config.ScalarMixedGetterEffects
import Leanux.Proofs.WG.Config.MultiMixedSource
import Leanux.Proofs.WG.Config.MultiMixedFrames
import Leanux.Proofs.WG.Config.MixedGetterClaims
import Leanux.Proofs.WG.Config.MixedGetterInputFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Actual fwmark/source-reset and selected scalar update followed by the full
mixed getter. Reset Stops are retained by this normal-return contract; later
-EINVAL preserves the first scalar writes. Static pagination premises concern
the explicit configured successor, while the final raw Device folds handoffs
over the actual source-cleared setter successor. -/
theorem fwmark_scalar_mixed_get_after_set (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (mark : Nat) (key psk : Key) (interval : Nat)
    (bad : Bool) (pid : PeerId) (sock : NlSock)
    (net : d.creatingNet = true)
    (found : d.peerHashtable.find? (·.1 == key) = some (key,pid))
    (resident : d.peers[pid]? = some (peers pid))
    (live : 0 < (peers pid).refcount) (bounded : (peers pid).refcount+1 < 2^31)
    (down : d.running = false)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (readable : ∀ q ∈ d.peerList, ∀ id ∈ (peers q).allowedipsList, d.nodes[id]? = some (nodes id))
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let updated := scalarRequestDevice {d with fwmark := mark} pid (peers pid) psk interval
    let configured := scalarPeerView peers pid psk interval
    ∀ ready : MixedPageReady updated configured nodes (mixedInitialRows updated configured) {hasWg := true},
    devicePrefixSpace updated ≤ NLMSG_GOODSIZE →
    MixedPlanFresh updated configured
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) →
    MixedPlanCursorData updated
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) →
    mixedPageReceiveCount
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) ≤ 4096 →
    Campaign2.Ensures (do
      let ret ← wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        let pages := mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready
        result = ((if bad then -EINVAL else 0),.ok (mixedGetterJson updated configured nodes)) ∧
        s.wg.nlSock7 = socketReadbackFinal sock updated ∧
        ∃ postSet, MultiMixedEffect d mark pid psk interval postSet ∧
          s.wg.device = some (mixedPagesDevice postSet pages) ∧
          CursorHeld postSet (mixedPagesDevice postSet pages) none) := by
  dsimp only
  intro ready headerFits fresh cursorData within
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
    let updated := scalarRequestDevice {d with fwmark := mark} pid (peers pid) psk interval
    let configured := scalarPeerView peers pid psk interval
    have outer := multiMixedEffect_outer d current mark pid psk interval effect
    have sameList : current.peerList = updated.peerList := by
      have h := congrArg Device.peerList outer; exact h
    have sameName : current.ifname = d.ifname := by
      have h := congrArg Device.ifname outer; exact h
    have sameIndex : current.ifindex = d.ifindex := by
      have h := congrArg Device.ifindex outer; exact h
    have sameNodes : current.nodes = updated.nodes := by
      have h := congrArg Device.nodes outer; exact h
    have sameSeq : current.peerAllowedips.seq = updated.peerAllowedips.seq := by
      have h := congrArg (fun x => x.peerAllowedips.seq) outer; exact h
    have sameSpace : devicePrefixSpace current = devicePrefixSpace updated := by
      have h := congrArg devicePrefixSpace outer; exact h
    have sameAttrs : deviceFixedAttrs current = deviceFixedAttrs updated := by
      have h := congrArg deviceFixedAttrs outer; exact h
    have generation : current.deviceUpdateGen = updated.deviceUpdateGen := by
      have h := congrArg Device.deviceUpdateGen outer; exact h
    have lookup := multiMixedEffect_getter_view d current mark pid (peers pid) psk interval effect resident
    obtain ⟨originalList,_,_,originalNodes,updatedResidents,ips⟩ :=
      scalarRequestDevice_mixed_effect {d with fwmark := mark} peers pid psk interval residents
    have updatedReadable : ∀ q ∈ updated.peerList, ∀ id ∈ (configured q).allowedipsList,
        updated.nodes[id]? = some (nodes id) := by
      intro q member id node
      rw [originalList] at member
      rw [ips] at node
      rw [originalNodes]
      exact readable q member id node
    let values := keyGetterPeers updated current configured
    have view := keyGetterPeers_frame updated current configured lookup updatedResidents
    have congruence := mixedGetter_data_congr updated current configured values sameList sameAttrs view.2 lookup nodes
    have currentReady : MixedPageReady current values nodes (mixedInitialRows current values) {hasWg := true} := by
      rw [congruence.1]
      exact (mixedPageReady_getter_congr updated current configured values sameSpace view.2 nodes _ _).mpr ready
    have pagesEq : mixedPages current values nodes (mixedInitialRows current values) {hasWg := true} currentReady =
        mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready := by
      have baselineReady : MixedPageReady updated configured nodes (mixedInitialRows current values) {hasWg := true} := by
        rw [congruence.1]
        exact ready
      have h := mixedPages_getter_congr updated current configured values sameSpace sameSeq view.2 nodes _ _ baselineReady currentReady
      simpa only [congruence.1] using h
    have currentResidents : ∀ q ∈ current.peerList, current.peers[q]? = some (values q) := by
      simpa only [sameList] using view.1
    have currentReadable : ∀ q ∈ current.peerList, ∀ id ∈ (values q).allowedipsList,
        current.nodes[id]? = some (nodes id) := by
      intro q member id node
      have h := view.2 q
      simp only [keyGetterPeerView,Prod.mk.injEq] at h
      rw [h.2.2.2.1] at node
      rw [sameNodes]
      exact updatedReadable q (sameList ▸ member) id node
    have currentFresh : MixedPlanFresh current values
        (mixedPages current values nodes (mixedInitialRows current values) {hasWg := true} currentReady) := by
      rw [pagesEq]
      exact (congruence.2.2.1 _).mpr fresh
    have currentData : MixedPlanCursorData current
        (mixedPages current values nodes (mixedInitialRows current values) {hasWg := true} currentReady) := by
      rw [pagesEq]
      exact (congruence.2.2.2 _).mpr cursorData
    have selection : selectsDevice middle current := by
      have selected : selectsDevice entry d := pre.2.2
      simpa only [selectsDevice,sameName,sameIndex,framed.2] using selected
    obtain ⟨dump,out,rest,getRun,dumped,retained,socket,restored⟩ := mixed_getter_returns current values nodes sock
      currentReady currentResidents currentReadable (by simpa only [sameSpace] using headerFits)
      currentFresh currentData idle emptyQueue (by simpa only [pagesEq] using within)
      middle next ⟨device,framed.1,selection⟩
    have selector : byIndex d = byIndex current := by simp only [byIndex,sameIndex]
    rw [setRun] at run
    change (((wgGetDevice (byIndex d)).run middle).run next >>=
      fun ((dump,out),rest) => Except.ok (((ret,dump),out),rest)) = _ at run
    rw [selector,getRun] at run
    cases run
    refine ⟨?_,?_,current,effect,?_,?_⟩
    · simp only [code,dumped,congruence.2.1]
      rfl
    · change final.nlSock7 = _
      change final.nlSock7 = socketReadbackFinal sock current at socket
      simpa only [socketReadbackFinal,generation] using socket
    · simpa only [pagesEq] using retained
    · simpa only [pagesEq] using restored

end Leanux.Proofs.WG.Config
