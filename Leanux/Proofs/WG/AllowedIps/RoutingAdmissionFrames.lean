import Leanux.Proofs.WG.AllowedIps.RoutingRxFrames
import Leanux.Proofs.Framing.WGReceiveHeaders

/-! Original receive admission is silent for routing, including normal error
cleanup. Resident peers may disappear; missing stores and record failures remain
original Stops. No packet/key/peer affiliation or initial residency is assumed. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.WG.Queues Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem peerGetMaybeZero_routing (peer : Option PeerId) :
    SameView routingView (peerGetMaybeZero peer) := by
  intro w result v hr
  have hb := ((hoare_iff_triple _ _ _).mpr (PeerBorrow.acquire_spec peer w.k) w result v rfl hr).2
  cases result with
  | none => change v.k = w.k at hb; simp [routingView, hb]
  | some pid =>
    obtain ⟨d, p, hd, hp, _, hk⟩ := hb
    have hs := routingState_insert_same d pid p {p with refcount := p.refcount + 1} hp rfl
    simp [routingView, hk, hd, hs]

theorem indexLookup_routing (kinds : List IndexKind) (index : Nat) :
    SameView routingView (indexLookup kinds index) := by
  apply SameView.of_wp
  intro s
  have hp := fun peer => (peerGetMaybeZero_routing peer).wp (fun t => t = s)
  have hb := (routing_kernel _ (Framing.indexBucket_sameKernel index)).wp (fun t => t = s)
  mvcgen [indexLookup, hp, hb, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜routingView w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView]

theorem newRxSkb_routing (pkt : RxPacket) : SameView routingView (newRxSkb pkt) := by
  apply SameView.of_wp
  intro s
  mvcgen [newRxSkb, getDev, getK, modifyDev, modifyK, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [routingView, routingState, Option.map_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

theorem enqueuePerDeviceAndPeerRx_routing (id : SkbId) :
    SameView routingView (enqueuePerDeviceAndPeerRx id) := by
  apply SameView.of_wp
  intro s
  have hp := fun pid => routing_getPeer (fun t => t = s) pid
  have hset := fun pid p => routing_setPeer (fun t => t = s) pid p
  have hr := (getRxSkb_routing id).wp (fun t => t = s)
  have hs := fun f => (setRxSkb_routing id f).wp (fun t => t = s)
  have hc := fun last => (routing_kernel _ (cpumaskNextOnlineFrom_sameKernel last)).wp (fun t => t = s)
  have hw := (routing_kernel _ (queueDeviceWork_sameKernel .decryptWorker)).wp (fun t => t = s)
  mvcgen [enqueuePerDeviceAndPeerRx, hp, hset, hr, hs, hc, hw,
    getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold routingView at *; simp_all [routingState, Option.bind_map, Function.comp_def]
  all_goals assumption

theorem consumeData_routing (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    RetainsRoutingCall (consumeData msg src ds) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hl := (indexLookup_routing [.keypair] (u32le msg 4)).wp P
  have hg := fun kp => (keypairGet_routing kp).wp P
  have hp := fun pid => (getPeer_routing pid).wp P
  have hn := fun pkt => (newRxSkb_routing pkt).wp P
  have he := fun id => (enqueuePerDeviceAndPeerRx_routing id).wp P
  have hq := fun id => (enqueuePerPeerRx_routing (pure ())
    (.of_same (SameView.pure routingView ())) id .dead).wp s
  have hk := fun kp => (keypairPut_routing kp false).wp P
  have hu := fun pid => (peerPut_retainsRouting pid).wp s
  have hf := fun id => (freeRxSkb_routing id).wp P
  mvcgen [consumeData, hl, hg, hp, hn, he, hq, hk, hu, hf,
    keypairGetCurrent, WG.orM, branch, branchCmp, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem cpumaskNextOnline_routing : SameView routingView cpumaskNextOnline := by
  apply SameView.of_wp
  intro s
  mvcgen [cpumaskNextOnline, getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [routingView, routingState, Option.map_map, Function.comp_def]
  all_goals assumption

theorem packetReceive_routing (msg : List UInt8) (src : SkbSource) :
    RetainsRoutingCall (packetReceive msg src) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hh := (routing_kernel _ (prepareSkbHeader_sameKernel msg)).wp P
  have hd := fun protocol bytes => (routing_kernel _ (ipTunnelGetDsfield_sameKernel protocol bytes)).wp P
  have hc := fun ds => (consumeData_routing msg src ds).wp s
  have hn := cpumaskNextOnline_routing.wp P
  have hw := (routing_kernel _ (queueDeviceWork_sameKernel .receiveWorker)).wp P
  have hm := (modifyDev_routing (fun d => {d with handshakeQueue := d.handshakeQueue ++ [(msg, src)], handshakeQueueLen := d.handshakeQueueLen + 1}) (fun _ => rfl)).wp P
  mvcgen [packetReceive, hh, hd, hc, hn, hw, hm, getDev, getK, branch, invariant, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold routingView at *; simp_all)
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem wgReceive_routing (msg : List UInt8) (src : SkbSource) :
    RetainsRoutingCall (wgReceive msg src) := by
  apply ProjectedAction.of_wp
  intro s
  have hp := (packetReceive_routing msg src).wp s
  mvcgen [wgReceive, hp, branch, unsupported]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

end Leanux.Proofs.WG.AllowedIps
