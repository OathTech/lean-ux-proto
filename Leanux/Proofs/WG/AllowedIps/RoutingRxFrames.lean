import Leanux.Proofs.WG.AllowedIps.RoutingTxFrames
import Leanux.Proofs.WG.Queues.RxPollPrefix
import Leanux.Proofs.WG.Queues.RxRingWorker

/-! Original receive completion, poll and decrypt-worker routing frames.
Callbacks have explicit routing contracts; the stack callback is discharged
concretely. Normal endpoints permit peer deletion and retain orphan owners. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.WG.Queues Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem getRxSkb_routing (id : SkbId) : SameView routingView (getRxSkb id) := by
  apply SameView.of_wp
  intro s
  mvcgen [getRxSkb, getDev, getK, invariant]

theorem setRxSkb_routing (id : SkbId) (f : RxPacket → RxPacket) :
    SameView routingView (setRxSkb id f) := by
  unfold setRxSkb
  exact (getRxSkb_routing id).bind fun _ => modifyDev_routing _ (fun _ => rfl)

theorem freeRxSkb_routing (id : SkbId) : SameView routingView (freeRxSkb id) := by
  unfold freeRxSkb
  exact (getRxSkb_routing id).bind fun _ => modifyDev_routing _ (fun _ => rfl)

theorem decryptPacket_routing (pkt : RxPacket) : SameView routingView (decryptPacket pkt) := by
  apply SameView.of_wp
  intro s
  have hc := fun d birth age => (routing_kernel _ (branchExpired_sameKernel d birth age)).wp (fun t => t = s)
  have hh := (routing_kernel _ (hiddenAlloc_sameKernel .skbCowDataRx)).wp (fun t => t = s)
  have hg := fun id => (getKeypair_routing id).wp (fun t => t = s)
  have hs := fun id k => (setKeypair_routing id k).wp (fun t => t = s)
  mvcgen [decryptPacket, hc, hh, hg, hs, WG.orM, branch, branchCmp, invariant]

theorem counterValidate_routing (kp : KeypairId) (nonce : Nat) :
    SameView routingView (counterValidate kp nonce) := by
  apply SameView.of_wp
  intro s
  have hg := (getKeypair_routing kp).wp (fun t => t = s)
  have hs := fun k => (setKeypair_routing kp k).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    counterValidate, hg, hs, branch, branchCmp, WG.orM, invariant]
  all_goals try exact ((⇓? _ w => ⌜routingView w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView]
  all_goals trivial

theorem receivedWithKeypair_routing (pid : PeerId) (kp : KeypairId) :
    SameView routingView (receivedWithKeypair pid kp) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_routing pid).wp (fun t => t = s)
  have hk := fun old => (keypairPut_routing old true).wp (fun t => t = s)
  have hp1 : ⦃fun w => ⌜routingView w = s⌝⦄
      (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
        (fun p => {p with keypairPrevious := p.keypairCurrent})
      ⦃⇓? _ w => ⌜routingView w = s⌝⦄ :=
    (modifyPeer_routing pid (fun p => {p with keypairPrevious := p.keypairCurrent}) (fun _ => rfl)).wp (fun t => t = s)
  have hp2 : ⦃fun w => ⌜routingView w = s⌝⦄
      (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
        (fun p => {p with keypairCurrent := some kp, keypairNext := none})
      ⦃⇓? _ w => ⌜routingView w = s⌝⦄ :=
    (modifyPeer_routing pid (fun p => {p with keypairCurrent := some kp, keypairNext := none}) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [receivedWithKeypair, hg, hk, hp1, hp2, branch, invariant]

theorem timersHandshakeComplete_routing (pid : PeerId) (site : HiddenSite) :
    SameView routingView (timersHandshakeComplete pid site) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hd := (delTimer_routing pid .retransmitHandshake).wp (fun t => t = s)
  have hh := (routing_kernel _ (hidden_sameKernel site)).wp (fun t => t = s)
  mvcgen [timersHandshakeComplete, hg, hs, hd, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView, routingState]

theorem timersAnyAuthenticatedPacketReceived_routing (pid : PeerId) :
    SameView routingView (timersAnyAuthenticatedPacketReceived pid) := delTimer_routing pid .newHandshake

theorem timersDataReceived_routing (pid : PeerId) : SameView routingView (timersDataReceived pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have ht := (modPeerTimer_routing .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS).wp (fun t => t = s)
  have hd := discard_view_spec routingView (fun t => t = s) _ ht
  mvcgen [timersDataReceived, hg, hs, ht, hd, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView, routingState]

theorem keepKeyFreshRx_routing (pid : PeerId) : RetainsRoutingCall (keepKeyFreshRx pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := routing_getPeer P pid
  have hs := fun p => routing_setPeer P pid p
  have hk := fun id => (getKeypair_routing id).wp P
  have ht := fun date delay => (routing_kernel _ (branchExpired_sameKernel .rxFreshExpired date delay)).wp P
  have hq := (sendQueuedHandshakeInitiation_routing pid false).wp s
  mvcgen [keepKeyFreshRx, hg, hs, hk, ht, hq, WG.andM, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, routingState]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem dishonest_routing (why : Dishonest) : SameView routingView (dishonest why) :=
  modifyDev_routing _ (fun d => by cases why <;> rfl)

theorem updateRxStats_routing (pid : PeerId) (len : Nat) :
    SameView routingView (updateRxStats pid len) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hd := (modifyDev_routing (fun d => {d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + len})
    (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [updateRxStats, hg, hs, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold routingView at *; simp_all [routingState]

theorem consumeDataDone_routing (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    RetainsRoutingCall (consumeDataDone pid pkt endpoint) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hep := (setPeerEndpoint_routing pid endpoint).wp P
  have hk := (receivedWithKeypair_routing pid pkt.keypair).wp P
  have hh := (timersHandshakeComplete_routing pid .walltimeLastHandshakeData).wp P
  have hst := (sendStagedPackets_routing pid).wp s
  have hf := (keepKeyFreshRx_routing pid).wp s
  have ha := (timersAnyAuthenticatedPacketReceived_routing pid).wp P
  have htr := (timersTraversal_routing pid).wp P
  have hdata := (timersDataReceived_routing pid).wp P
  have hstats := fun len => (updateRxStats_routing pid len).wp P
  have herr := fun why => (dishonest_routing why).wp P
  have hecn := fun protocol outer bytes => (routing_kernel _ (inetEcnDecapsulate_sameKernel protocol outer bytes)).wp P
  have hl := fun protocol bytes => (lookupSrc_routing protocol bytes).wp P
  have hp := fun peer => (peerPut_retainsRouting peer).wp s
  mvcgen [consumeDataDone, hep, hk, hh, hst, hf, ha, htr, hdata, hstats, herr, hecn, hl, hp,
    WG.andM, WG.orM, branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold routingView at *; simp_all)
  all_goals subst s
  all_goals exact RetainsRouting.refl _

private theorem peekRxQueue_routing (pid : PeerId) : SameView routingView (peekRxQueue pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hq := fun (q : PrevQueue SkbId) => (routing_kernel _ (prevQueuePeek_sameKernel q)).wp (fun t => t = s)
  mvcgen [peekRxQueue, hg, hs, hq]
  all_goals simp_all

private theorem dropRxQueue_routing (pid : PeerId) : SameView routingView (dropRxQueue pid) := by
  simp only [dropRxQueue, getPeer_twice]
  exact modifyPeer_routing pid _ (fun _ => rfl)

private theorem completeRxQueue_routing (pid : PeerId) : SameView routingView (completeRxQueue pid) :=
  modifyPeer_routing pid _ (fun _ => rfl)

theorem groNormalList_routing (cb : List (List UInt8) → M Unit)
    (hc : ∀ xs, RetainsRoutingCall (cb xs)) (g : GroState) : RetainsRoutingCall (groNormalList cb g) := by
  apply ProjectedAction.of_wp
  intro s
  have hcb := fun xs => (hc xs).wp s
  mvcgen [groNormalList, hcb]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem groNormalOne_routing (cb : List (List UInt8) → M Unit)
    (hc : ∀ xs, RetainsRoutingCall (cb xs)) (g : GroState) (pkt : List UInt8) (segs : Nat) :
    RetainsRoutingCall (groNormalOne cb g pkt segs) := by
  apply ProjectedAction.of_wp
  intro s
  have hl := fun g => (groNormalList_routing cb hc g).wp s
  mvcgen [groNormalOne, hl]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem napiGroReceive_routing (cb : List (List UInt8) → M Unit)
    (hc : ∀ xs, RetainsRoutingCall (cb xs)) (g : GroState) (pkt : List UInt8) :
    RetainsRoutingCall (napiGroReceive cb g pkt) := by
  apply ProjectedAction.of_wp
  intro s
  have hn := fun g pkt segs => (groNormalOne_routing cb hc g pkt segs).wp s
  mvcgen [napiGroReceive, hn, unsupported]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem napiGroFlushAll_routing (cb : List (List UInt8) → M Unit)
    (hc : ∀ xs, RetainsRoutingCall (cb xs)) (g : GroState) :
    RetainsRoutingCall (napiGroFlushAll cb g) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hn := fun g pkt segs => (groNormalOne_routing cb hc g pkt segs).wp s
  have hl := fun g => (groNormalList_routing cb hc g).wp s
  have hlist (α β : Type) := list_view_spec routingView (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hlist, napiGroFlushAll, hn, hl]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem rxPoll_routing (pid : PeerId) (budget : Nat) (cb : List (List UInt8) → M Unit)
    (hc : ∀ xs, RetainsRoutingCall (cb xs)) : RetainsRoutingCall (rxPoll pid budget cb) := by
  rw [← rxPollGrouped_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hp := (peekRxQueue_routing pid).wp P
  have hdrop := (dropRxQueue_routing pid).wp P
  have hcomplete := (completeRxQueue_routing pid).wp P
  have hr := fun id => (getRxSkb_routing id).wp P
  have hctr := fun key nonce => (counterValidate_routing key nonce).wp P
  have he := fun src => (routing_kernel _ (endpointFromSkb_sameKernel src)).wp P
  have hd := fun pkt ep => (consumeDataDone_routing pid pkt ep).wp s
  have hg := fun g pkt => (napiGroReceive_routing cb hc g pkt).wp s
  have hf := fun g => (napiGroFlushAll_routing cb hc g).wp s
  have hk := fun kp => (keypairPut_routing kp false).wp P
  have hu := (peerPut_retainsRouting (some pid)).wp s
  have hx := fun id => (freeRxSkb_routing id).wp P
  have hl (α β : Type) := list_view_spec routingView (α := α) (β := β) P
  simp only [rxPollGrouped, Std.Legacy.Range.forIn_eq_forIn_range']
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    hp, hdrop, hcomplete, hr, hctr, he, hd, hg, hf, hk, hu, hx, WG.andM, branch, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem actualRxPoll_routing (pid : PeerId) (budget : Nat) :
    RetainsRoutingCall (rxPoll pid budget (fun xs => xs.forM Leanux.Env.deliverInner)) :=
  rxPoll_routing pid budget _ stackForM_routing

theorem enqueuePerPeerRx_routing (irq : M Unit) (hi : RetainsRoutingCall irq)
    (id : SkbId) (state : PacketState) : RetainsRoutingCall (enqueuePerPeerRx irq id state) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hk := fun id => (getKeypair_routing id).wp P
  have hget := fun pid => (peerGet_routing pid).wp P
  have hp := fun pid => routing_getPeer P pid
  have hs := fun pid p => routing_setPeer P pid p
  have hir := hi.wp s
  have hput := fun pid => (peerPut_retainsRouting pid).wp s
  have hw := fun o => (ownerDeref_routing o).wp P
  mvcgen [hw, enqueuePerPeerRx, hk, hget, hp, hs, hir, hput,
    setRxSkb, getRxSkb, getDev, getK, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, routingState, Option.bind_map, Function.comp_def]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

private theorem decryptPoll_routing : SameView routingView RxRing.pollSource := by
  apply SameView.of_wp
  intro s
  have hm := fun ring => (modifyDev_routing (fun d => {d with decryptQueue := ring}) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [RxRing.pollSource, hm, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView]

theorem decryptStep_routing (softirq irq : M Unit)
    (hs : RetainsRoutingCall softirq) (hi : RetainsRoutingCall irq) :
    RetainsRoutingCall (decryptStep softirq irq) := by
  rw [← RxRing.stepSource_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hsoft := hs.wp s
  have hp := decryptPoll_routing.wp P
  have hg := fun id => (getRxSkb_routing id).wp P
  have hd := fun pkt => (decryptPacket_routing pkt).wp P
  have hset := fun id f => (setRxSkb_routing id f).wp P
  have hq := fun id state => (enqueuePerPeerRx_routing irq hi id state).wp s
  mvcgen [RxRing.stepSource, hsoft, hp, hg, hd, hset, hq, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem decryptIter_routing (softirq irq : M Unit) (need : M Bool)
    (hs : RetainsRoutingCall softirq) (hi : RetainsRoutingCall irq) (hn : RetainsRoutingCall need) :
    RetainsRoutingCall (decryptIter softirq irq need) := by
  apply workerIter_routing _ _ _ _ (decryptStep_routing softirq irq hs hi)
  apply ProjectedAction.of_wp
  intro s
  have hneed := hn.wp s
  mvcgen [hneed, branch]
  subst s
  exact RetainsRouting.refl _

end Leanux.Proofs.WG.AllowedIps
