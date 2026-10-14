import Leanux.Proofs.WG.AllowedIps.RoutingSocketFrames

/-! Concrete routing frames for the handshake/clear work executed by peer
removal. Only actual normal returns carry a frame; recorded failures stay intact. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1200000
set_option pp.structureInstances false

theorem modifyPeer_routing (pid : PeerId) (f : Peer → Peer)
    (hl : ∀ p, (f p).allowedipsList = p.allowedipsList) :
    SameView routingView (do let p ← getPeer pid; setPeer pid (f p)) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  mvcgen [hg, hs]
  all_goals simp_all [hl]

theorem setPeerEndpoint_routing (pid : PeerId) (e : Endpoint) : SameView routingView (setPeerEndpoint pid e) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hn := (requireNotPending_routing pid "changing the endpoint").wp (fun t => t = s)
  have he := fun old => (routing_kernel _ (endpointEq_sameKernel e old)).wp (fun t => t = s)
  have hc := (dstCacheReset_routing pid).wp (fun t => t = s)
  mvcgen [setPeerEndpoint, hg, hs, hn, he, hc, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState]
  all_goals try assumption

theorem armTimer_routing (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    SameView routingView (armTimer pid timer delay jc) := by
  rw [armTimer_source pid timer delay jc]
  apply SameView.bind (routing_kernel _ (timerArmExpiry_sameKernel pid timer delay jc))
  intro expiry
  exact modifyPeer_routing pid (fun p => p.setTimer timer (some expiry))
    (fun p => by cases timer <;> rfl)

theorem delTimer_routing (pid : PeerId) (timer : PeerTimer) : SameView routingView (delTimer pid timer) :=
  modifyPeer_routing pid (fun p => p.setTimer timer none)
    (fun p => by cases timer <;> rfl)

theorem modPeerTimerGuard_routing (pid : PeerId) : SameView routingView (modPeerTimerGuard pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_routing pid).wp (fun t => t = s)
  mvcgen [modPeerTimerGuard, getDev, getK, hg, WG.andM, branch, invariant]

theorem modPeerTimer_routing (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView routingView (modPeerTimer site pid timer delay) := by
  apply SameView.of_wp
  intro s
  have hg := (modPeerTimerGuard_routing pid).wp (fun t => t = s)
  have ha := fun jc => (armTimer_routing pid timer delay jc).wp (fun t => t = s)
  have hc := (routing_kernel _ (callerJiffies_sameKernel site)).wp (fun t => t = s)
  mvcgen [modPeerTimer, hg, ha, hc]

theorem timersTraversal_routing (pid : PeerId) : SameView routingView (timersTraversal pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_routing pid).wp (fun t => t = s)
  have ht := fun delay => (modPeerTimer_routing .timerJiffiesTraversal pid .persistentKeepalive delay).wp (fun t => t = s)
  have hd := fun delay => discard_view_spec routingView (fun t => t = s) _ (ht delay)
  mvcgen [timersTraversal, hg, ht, hd, branchCmp]


theorem timersAnyAuthenticatedPacketSent_routing (pid : PeerId) :
    SameView routingView (timersAnyAuthenticatedPacketSent pid) := delTimer_routing pid .sendKeepalive

theorem timersHandshakeInitiated_routing (pid : PeerId) :
    SameView routingView (timersHandshakeInitiated pid) := by
  apply SameView.of_wp
  intro s
  have hc := (routing_kernel _ (callerJiffies_sameKernel .timerJiffiesHandshakeInitiated)).wp (fun t => t = s)
  have hj := (routing_kernel _ (jitterBelowRekeyTimeout_sameKernel .retransmitJitter)).wp (fun t => t = s)
  have hg := (modPeerTimerGuard_routing pid).wp (fun t => t = s)
  have ha := fun n jc => (armTimer_routing pid .retransmitHandshake n jc).wp (fun t => t = s)
  mvcgen [timersHandshakeInitiated, hc, hj, hg, ha]

theorem indexInsert_routing (pid : PeerId) (kind : IndexKind) :
    SameView routingView (indexInsert pid kind) := by
  apply (indexInsert_sameIndexKernel pid kind).of_factor
    (fun k : Kernel => k.wg.map routingState) routingView
  intro w
  simp [routingView, indexKernelView, indexKernel, routingState, Option.map_map, Function.comp_def]
  rfl

theorem createInitiation_routing (pid : PeerId) : SameView routingView (createInitiation pid) := by
  apply SameView.of_wp
  intro s
  have hg := fun pid => routing_getPeer (fun t => t = s) pid
  have hs := fun pid p => routing_setPeer (fun t => t = s) pid p
  have hh := fun site => (routing_kernel _ (hidden_sameKernel site)).wp (fun t => t = s)
  have hp := fun k => (routing_kernel _ (generatePublic_sameKernel k)).wp (fun t => t = s)
  have he := fun b e ck h => (routing_kernel _ (messageEphemeral_sameKernel b e ck h)).wp (fun t => t = s)
  have hd := fun b ck p q => (routing_kernel _ (mixDh_sameKernel b ck p q)).wp (fun t => t = s)
  have hpre := fun ck p => (routing_kernel _ (mixPrecomputedDh_sameKernel ck p)).wp (fun t => t = s)
  have hi := (indexInsert_routing pid .handshake).wp (fun t => t = s)
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  mvcgen [hg, hs, hh, hp, he, hd, hpre, hi, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState]
  all_goals try assumption

theorem addMacToPacket_routing (pid : PeerId) (msg : List UInt8) :
    SameView routingView (addMacToPacket pid msg) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have he := fun d b n f => (routing_kernel _ (branchExpired_sameKernel d b n f)).wp (fun t => t = s)
  mvcgen [addMacToPacket, hg, hs, he, branch, WG.andM]
  all_goals simp_all

theorem sendBufferToPeer_routing (pid : PeerId) (bytes : List UInt8) :
    SameView routingView (sendBufferToPeer pid bytes) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have ha := fun site => (routing_kernel _ (hiddenAlloc_sameKernel site)).wp (fun t => t = s)
  have h4 := fun e => (send4_routing e (some pid) bytes HANDSHAKE_DSCP true).wp (fun t => t = s)
  have h6 := fun e => (send6_routing e (some pid) bytes HANDSHAKE_DSCP true).wp (fun t => t = s)
  mvcgen [sendBufferToPeer, hg, hs, ha, h4, h6, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState]
  all_goals try assumption

theorem sendHandshakeInitiation_routing (pid : PeerId) : SameView routingView (sendHandshakeInitiation pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have he := fun date => (routing_kernel _ (branchExpired_sameKernel .initRateLimited date REKEY_TIMEOUT (!·))).wp (fun t => t = s)
  have hc := fun site => (routing_kernel _ (hiddenClock64_sameKernel site)).wp (fun t => t = s)
  have hi := (createInitiation_routing pid).wp (fun t => t = s)
  have hm := fun msg => (addMacToPacket_routing pid msg).wp (fun t => t = s)
  have ht := (timersTraversal_routing pid).wp (fun t => t = s)
  have ha := (timersAnyAuthenticatedPacketSent_routing pid).wp (fun t => t = s)
  have hb := fun msg => (sendBufferToPeer_routing pid msg).wp (fun t => t = s)
  have hj := (timersHandshakeInitiated_routing pid).wp (fun t => t = s)
  mvcgen [sendHandshakeInitiation, hg, hs, he, hc, hi, hm, ht, ha, hb, hj, branch, invariant]
  all_goals try simp_all

theorem handshakeZero_routing (pid : PeerId) : SameView routingView (handshakeZero pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  mvcgen [handshakeZero, hg, hs]
  all_goals simp_all

theorem keypairsClear_routing (pid : PeerId) : SameView routingView (keypairsClear pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hk := fun kp => (keypairPut_routing kp true).wp (fun t => t = s)
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  mvcgen [hg, hs, hk]
  all_goals simp_all

theorem handshakeClear_routing (pid : PeerId) : SameView routingView (handshakeClear pid) :=
  (indexRemove_routing pid .handshake).bind (fun _ => handshakeZero_routing pid)

theorem handshakeSendWorker_routing (pid : PeerId) : RetainsRoutingCall (handshakeSendWorker pid) := by
  apply ProjectedAction.of_wp
  intro s
  have hi := (sendHandshakeInitiation_routing pid).wp (RetainsRouting s)
  have hp := (peerPut_retainsRouting (some pid)).wp s
  mvcgen [handshakeSendWorker, hi, hp]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem queuedExpiredZeroKeyMaterial_routing (pid : PeerId) : RetainsRoutingCall (queuedExpiredZeroKeyMaterial pid) := by
  apply ProjectedAction.of_wp
  intro s
  have hh := (handshakeClear_routing pid).wp (RetainsRouting s)
  have hk := (keypairsClear_routing pid).wp (RetainsRouting s)
  have hp := (peerPut_retainsRouting (some pid)).wp s
  mvcgen [queuedExpiredZeroKeyMaterial, hh, hk, hp]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

end Leanux.Proofs.WG.AllowedIps
