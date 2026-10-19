import Leanux.Proofs.WG.Config.PortMixedGetterFrames
import Leanux.Proofs.WG.Config.MixedGetterInputFrames
import Leanux.Proofs.WG.Config.PeerKeyGetterFrames
import Leanux.Proofs.WG.Config.MixedGetterClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The existing mixed getter continuation transported from a static serializer
baseline to the actual device. No native setter or getter is replayed. -/
theorem mixed_getter_fields_returns (base current : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (sock : NlSock)
    (fields : withoutPeers current = withoutPeers base)
    (lookup : ∀ q : PeerId, (current.peers[q]?).map keyGetterPeerView =
      (base.peers[q]?).map keyGetterPeerView)
    (residents : ∀ q ∈ base.peerList, base.peers[q]? = some (peers q))
    (readable : ∀ pid ∈ base.peerList, ∀ id ∈ (peers pid).allowedipsList,
      base.nodes[id]? = some (nodes id))
    (ready : MixedPageReady base peers nodes (mixedInitialRows base peers) {hasWg := true})
    (headerFits : devicePrefixSpace base ≤ NLMSG_GOODSIZE)
    (fresh : MixedPlanFresh base peers
      (mixedPages base peers nodes (mixedInitialRows base peers) {hasWg := true} ready))
    (cursorData : MixedPlanCursorData base
      (mixedPages base peers nodes (mixedInitialRows base peers) {hasWg := true} ready))
    (within : mixedPageReceiveCount
      (mixedPages base peers nodes (mixedInitialRows base peers) {hasWg := true} ready) ≤ 4096)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let pages := mixedPages base peers nodes (mixedInitialRows base peers) {hasWg := true} ready
    Campaign2.Returns (wgGetDevice (byIndex base))
      (fun s => s.wg.device = some current ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s base)
      (fun result s => result = .ok (mixedGetterJson base peers nodes) ∧
        ∃ values : PeerId → Peer,
          (∀ q ∈ base.peerList, current.peers[q]? = some (values q)) ∧
          (∀ q, keyGetterPeerView (values q) = keyGetterPeerView (peers q)) ∧
          s.wg.device = some (mixedPagesDevice current pages) ∧
          s.wg.nlSock7 = socketReadbackFinal sock current ∧
          CursorHeld current (mixedPagesDevice current pages) none) := by
  dsimp only
  intro middle next pre
  let values := keyGetterPeers base current peers
  obtain ⟨currentResidents,same⟩ := keyGetterPeers_frame base current peers lookup residents
  change (∀ q ∈ base.peerList, current.peers[q]? = some (values q)) at currentResidents
  change (∀ q, keyGetterPeerView (values q) = keyGetterPeerView (peers q)) at same
  have details (q : PeerId) :
      (values q).remoteStatic = (peers q).remoteStatic ∧
      peerFixedAttrs (values q) = peerFixedAttrs (peers q) ∧
      peerFixedSpace (values q) = peerFixedSpace (peers q) ∧
      (values q).allowedipsList = (peers q).allowedipsList ∧
      (values q).refcount = (peers q).refcount ∧
      (values q).isDead = (peers q).isDead := by
    simpa only [keyGetterPeerView,Prod.mk.injEq] using same q
  have members : current.peerList = base.peerList := by
    have h := congrArg Device.peerList fields
    exact h
  have space : devicePrefixSpace current = devicePrefixSpace base := by
    have h := congrArg devicePrefixSpace fields
    exact h
  have index : current.ifindex = base.ifindex := by
    have h := congrArg Device.ifindex fields
    exact h
  have name : current.ifname = base.ifname := by
    have h := congrArg Device.ifname fields
    exact h
  have attrs : deviceFixedAttrs current = deviceFixedAttrs base := by
    have h := congrArg deviceFixedAttrs fields
    exact h
  have sequence : current.peerAllowedips.seq = base.peerAllowedips.seq :=
    by have h := congrArg (fun d : Device => d.peerAllowedips.seq) fields; exact h
  have nodesEq : current.nodes = base.nodes := by
    have h := congrArg Device.nodes fields
    exact h
  obtain ⟨rowsEq,json,freshEq,cursorEq⟩ := mixedGetter_data_congr base current
    peers values members attrs same lookup nodes
  have translatedReady : MixedPageReady current values nodes
      (mixedInitialRows base peers) {hasWg := true} :=
    (mixedPageReady_getter_congr base current peers values space same nodes _ _).mpr ready
  have currentReady : MixedPageReady current values nodes (mixedInitialRows current values) {hasWg := true} := by
    simpa only [rowsEq] using translatedReady
  have plan : mixedPages current values nodes (mixedInitialRows current values) {hasWg := true} currentReady =
      mixedPages base peers nodes (mixedInitialRows base peers) {hasWg := true} ready := by
    simpa only [rowsEq] using mixedPages_getter_congr base current peers values space
      sequence same nodes _ {hasWg := true} ready translatedReady
  have selection : ClaimView.selectsDevice (Campaign2.snapshot middle next) current := by
    simpa only [ClaimView.selectsDevice,index,name] using pre.2.2
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
      middle next ⟨pre.1,pre.2.1,selection⟩
  have selector : byIndex base = byIndex current := by simp [byIndex,index]
  refine ⟨dump,out,rest,?_,?_,values,currentResidents,same,?_,finalSocket,?_⟩
  · simpa only [selector] using getRun
  · simpa only [json] using dumped
  · simpa only [plan] using finalDevice
  · simpa only [plan] using held

end Leanux.Proofs.WG.Config
