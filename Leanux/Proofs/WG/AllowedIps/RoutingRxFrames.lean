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

theorem decryptPacket_routing (pkt : RxPacket) : SameView routingView (decryptPacket pkt) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => (fun t => t = s) (routingView w)) (fun _ w => (fun t => t = s) (routingView w)) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hc := fun d birth age => (branchExpired_sameWGWorld d birth age).wp (fun w => routingView w = s)
  have hg := fun id => (getKeypair_routing id).wp (fun t => t = s)
  have hs := fun id k => (setKeypair_routing id k).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, decryptPacket, hc, hg, hs, WG.orM, branch, branchCmp, invariant]

theorem counterValidate_routing (kp : KeypairId) (nonce : Nat) :
    SameView routingView (counterValidate kp nonce) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => (fun t => t = s) (routingView w)) (fun _ w => (fun t => t = s) (routingView w)) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hg := (getKeypair_routing kp).wp (fun t => t = s)
  have hs := fun k => (setKeypair_routing kp k).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec (m := AmbientM) routingView (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, -Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    counterValidate, hg, hs, branch, branchCmp, WG.orM, invariant]
  all_goals try exact ((⇓? _ w => ⌜routingView w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView]
  all_goals trivial

theorem receivedWithKeypair_routing (pid : PeerId) (kp : KeypairId) :
    SameView routingView (receivedWithKeypair pid kp) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => (fun t => t = s) (routingView w)) (fun _ w => (fun t => t = s) (routingView w)) := hoare_liftAmbient a _
  unfold Hoare at ambient
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
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, receivedWithKeypair, hg, hk, hp1, hp2, branch, invariant]

theorem timersHandshakeComplete_routing (pid : PeerId) (site : HiddenSite) :
    SameView routingView (timersHandshakeComplete pid site) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => (fun t => t = s) (routingView w)) (fun _ w => (fun t => t = s) (routingView w)) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hd := (delTimer_routing pid .retransmitHandshake).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, timersHandshakeComplete, hg, hs, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView, routingState]

theorem timersAnyAuthenticatedPacketReceived_routing (pid : PeerId) :
    SameView routingView (timersAnyAuthenticatedPacketReceived pid) := delTimer_routing pid .newHandshake

theorem timersDataReceived_routing (pid : PeerId) : SameView routingView (timersDataReceived pid) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => (fun t => t = s) (routingView w)) (fun _ w => (fun t => t = s) (routingView w)) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have ht := (modPeerTimer_routing .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS).wp (fun t => t = s)
  have hd := discard_view_spec (m := AmbientM) routingView (fun t => t = s) _ ht
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, timersDataReceived, hg, hs, ht, hd, getDev, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView, routingState]

theorem keepKeyFreshRx_routing (pid : PeerId) : RetainsRoutingCall (keepKeyFreshRx pid) := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => RetainsRouting s (routingView w)) (fun _ w => RetainsRouting s (routingView w)) := hoare_liftAmbient a _
  unfold Hoare at ambient
  let P := RetainsRouting s
  have hg := routing_getPeer P pid
  have hs := fun p => routing_setPeer P pid p
  have hk := fun id => (getKeypair_routing id).wp P
  have ht := fun date delay => (branchExpired_sameWGWorld .rxFreshExpired date delay).wp (fun w => P (routingView w))
  have hq := RetainsRoutingCall.wp (sendQueuedHandshakeInitiation_routing pid false) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, keepKeyFreshRx, hg, hs, hk, ht, hq, WG.andM, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem dishonest_routing (why : Dishonest) : SameView routingView (dishonest why) :=
  modifyDev_routing _ (fun d => by cases why <;> rfl)

theorem updateRxStats_routing (pid : PeerId) (len : Nat) :
    SameView routingView (updateRxStats pid len) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => (fun t => t = s) (routingView w)) (fun _ w => (fun t => t = s) (routingView w)) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hd := (modifyDev_routing (fun d => {d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + len})
    (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, updateRxStats, hg, hs, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold routingView at *; simp_all [routingState]

theorem consumeDataDone_routing (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    RetainsRoutingCall (consumeDataDone pid pkt endpoint) := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => RetainsRouting s (routingView w)) (fun _ w => RetainsRouting s (routingView w)) := hoare_liftAmbient a _
  unfold Hoare at ambient
  let P := RetainsRouting s
  have hep := (setPeerEndpoint_routing pid endpoint).wp P
  have hk := (receivedWithKeypair_routing pid pkt.keypair).wp P
  have hh := (timersHandshakeComplete_routing pid .walltimeLastHandshakeData).wp P
  have hst := RetainsRoutingCall.wp (sendStagedPackets_routing pid) s
  have hf := RetainsRoutingCall.wp (keepKeyFreshRx_routing pid) s
  have ha := (timersAnyAuthenticatedPacketReceived_routing pid).wp P
  have htr := (timersTraversal_routing pid).wp P
  have hdata := (timersDataReceived_routing pid).wp P
  have hstats := fun len => (updateRxStats_routing pid len).wp P
  have herr := fun why => (dishonest_routing why).wp P
  have hecn := fun protocol outer bytes => (routing_kernel _ (inetEcnDecapsulate_sameWGStore protocol outer bytes)).wp P
  have hl := fun protocol bytes => (lookupSrc_routing protocol bytes).wp P
  have hp := fun peer => RetainsRoutingCall.wp (peerPut_retainsRouting peer) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, consumeDataDone, hep, hk, hh, hst, hf, ha, htr, hdata, hstats, herr, hecn, hl, hp,
    WG.andM, WG.orM, branch]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold routingView at *; simp_all)
  all_goals subst s
  all_goals exact RetainsRouting.refl _

private theorem peekRxQueue_routing (pid : PeerId) : SameView routingView (peekRxQueue pid) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => (fun t => t = s) (routingView w)) (fun _ w => (fun t => t = s) (routingView w)) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hq := fun (q : PrevQueue SkbId) => (routing_kernel _ (prevQueuePeek_sameWGStore q)).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, peekRxQueue, hg, hs, hq]
  all_goals simp_all

private theorem dropRxQueue_routing (pid : PeerId) : SameView routingView (dropRxQueue pid) := by
  simp only [dropRxQueue, getPeer_twice]
  exact modifyPeer_routing pid _ (fun _ => rfl)

private theorem completeRxQueue_routing (pid : PeerId) : SameView routingView (completeRxQueue pid) :=
  modifyPeer_routing pid _ (fun _ => rfl)

theorem groNormalList_routing (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, ProductRetainsRoutingCall (cb xs)) (g : GroState) : ProductRetainsRoutingCall (groNormalList cb g) := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg)) (fun _ w => RetainsRouting s (routingView w.wg)) := productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  have hcb := fun xs => RetainsRoutingCall.wp (hc xs) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, groNormalList, hcb]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem groNormalOne_routing (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, ProductRetainsRoutingCall (cb xs)) (g : GroState) (pkt : List UInt8) (segs : Nat) :
    ProductRetainsRoutingCall (groNormalOne cb g pkt segs) := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg)) (fun _ w => RetainsRouting s (routingView w.wg)) := productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  have hl := fun g => RetainsRoutingCall.wp (groNormalList_routing cb hc g) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, groNormalOne, hl]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem napiGroReceive_routing (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, ProductRetainsRoutingCall (cb xs)) (g : GroState) (pkt : List UInt8) :
    ProductRetainsRoutingCall (napiGroReceive cb g pkt) := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg)) (fun _ w => RetainsRouting s (routingView w.wg)) := productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  have hn := fun g pkt segs => RetainsRoutingCall.wp (groNormalOne_routing cb hc g pkt segs) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, napiGroReceive, hn, unsupported]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem napiGroFlushAll_routing (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, ProductRetainsRoutingCall (cb xs)) (g : GroState) :
    ProductRetainsRoutingCall (napiGroFlushAll cb g) := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg)) (fun _ w => RetainsRouting s (routingView w.wg)) := productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  let P := RetainsRouting s
  have hn := fun g pkt segs => RetainsRoutingCall.wp (groNormalOne_routing cb hc g pkt segs) s
  have hl := fun g => RetainsRoutingCall.wp (groNormalList_routing cb hc g) s
  have hlist (α β : Type) := list_view_spec (m := Except Stop) (fun w : World => routingView w.wg) (α := α) (β := β) P
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, -Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hlist, napiGroFlushAll, hn, hl]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w.wg)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem rxPoll_routing (pid : PeerId) (budget : Nat) (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, ProductRetainsRoutingCall (cb xs)) : ProductRetainsRoutingCall (rxPoll pid budget cb) := by
  rw [← rxPollGrouped_eq]
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg)) (fun _ w => RetainsRouting s (routingView w.wg)) := productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  let P := RetainsRouting s
  have native {α : Type} (a : WG.M α) (ha : SameView routingView a) :
      Hoare (liftWG a) (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    (sameView_liftWG (fun w => routingView w.wg) routingView a ha (fun _ _ _ h => h)).wp P
  unfold Hoare at native
  have nativeSkb {α : Type} (a : SkbM α) : SameView routingView (liftSkb a) := by
    intro initial
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi
  have skb {α : Type} (a : SkbM α) := native (liftSkb a) (nativeSkb a)
  have go (a b : WG.M Bool) (ha : SameView routingView (WG.andM a b)) :
      Hoare (liftWG (WG.andM a b))
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) := native _ ha
  unfold Hoare at go
  have hp := native _ (peekRxQueue_routing pid)
  have hdrop := native _ (dropRxQueue_routing pid)
  have hcomplete := native _ (completeRxQueue_routing pid)
  have hctr := fun key nonce => native _ (counterValidate_routing key nonce)
  have he := fun src => native _ (routing_kernel _ (endpointFromSkb_sameWGStore src))
  have hd (pkt : RxPacket) (ep : Endpoint) :
      Hoare (liftWG (consumeDataDone pid pkt ep))
        (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    RetainsRoutingCall.wp ((consumeDataDone_routing pid pkt ep).liftWG) s
  unfold Hoare at hd
  have hg := fun g pkt => RetainsRoutingCall.wp (napiGroReceive_routing cb hc g pkt) s
  have hf := fun g => RetainsRoutingCall.wp (napiGroFlushAll_routing cb hc g) s
  have hk := fun kp => native _ (keypairPut_routing kp false)
  have hu : Hoare (liftWG (peerPut (some pid)))
      (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    RetainsRoutingCall.wp ((peerPut_retainsRouting (some pid)).liftWG) s
  unfold Hoare at hu
  have hl (α β : Type) := list_view_spec (m := Except Stop) (fun w : World => routingView w.wg) (α := α) (β := β) P
  have lift {α : Type} (a : WG.M α) : (liftM a : Leanux.M α) = liftWG a := rfl
  simp only [rxPollGrouped, Std.Legacy.Range.forIn_eq_forIn_range', lift]
  mvcgen [getRxSkb, setRxSkb, freeRxSkb, skb, liftM, -Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, -Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    go, hp, hdrop, hcomplete, hctr, he, hd, hg, hf, hk, hu]
  all_goals try
    apply SameView.of_wp
    intro initial
    have hs := fun (a : SkbM RxPacket) => (nativeSkb a).wp (fun v => v = initial)
    mvcgen [WG.andM, getRxSkb, hs, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜P (routingView w.wg)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem actualRxPoll_routing (pid : PeerId) (budget : Nat) :
    ProductRetainsRoutingCall (rxPoll pid budget (fun xs => xs.forM Leanux.Env.deliverInner)) :=
  rxPoll_routing pid budget _ stackForM_routing

theorem enqueuePerPeerRx_routing (irq : Leanux.M Unit) (hi : ProductRetainsRoutingCall irq)
    (id : SkbId) (state : PacketState) : ProductRetainsRoutingCall (enqueuePerPeerRx irq id state) := by
  let before : WG.M PeerId := do
    let pid ← IndexOwner.peerDeref (.keypair (← getRxSkb id).keypair)
    peerGet pid
    let p ← getPeer pid
    if !(p.rxQueue.all.contains id) then
      invariant "a decrypted packet that is not on its peer's rx_queue"
    setRxSkb id fun q => {q with state}
    setPeer pid {p with napiScheduled := true}
    pure pid
  have before_frame : SameView routingView before := by
    apply SameView.of_wp
    intro initial
    have skb {α : Type} (a : SkbM α) :
        Hoare (liftSkb a) (fun w => routingView w = initial)
          (fun _ w => routingView w = initial) := by
      apply hoare_liftSkb a
      intro w d store hi hd
      unfold routingView at hi ⊢
      simpa only [hd, Option.map_some, routingState] using hi
    unfold Hoare at skb
    have hg := fun pid => (peerGet_routing pid).wp (fun v => v = initial)
    have hp := routing_getPeer (fun v => v = initial)
    have hs := routing_setPeer (fun v => v = initial)
    have hw := fun o => (ownerDeref_routing o).wp (fun v => v = initial)
    mvcgen [before, getRxSkb, setRxSkb, skb, hg, hp, hs, hw,
      invariant, AmbientM.invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals try simp_all
    all_goals
      have lists (g : WGWorld) (pid : PeerId) :
          (g.dev.bind fun d => d.peers[pid]?.map (·.allowedipsList)) =
            (routingView g).bind (fun v => v.lists pid) := by
        simp [routingView, routingState, Option.bind_map, Function.comp_def]
      simp only [lists] at *
      rcases ‹routingView _ = initial ∧ _› with ⟨he, hl⟩
      simp_all
  have factor : enqueuePerPeerRx irq id state =
      (do let pid ← liftWG before; irq; liftWG (peerPut (some pid))) := by
    have lift {α : Type} (a : WG.M α) : (liftM a : Leanux.M α) = liftWG a := rfl
    have ambientLift {α : Type} (a : AmbientM α) :
        liftWG (monadLift a : WG.M α) = (monadLift a : Leanux.M α) :=
      liftWG_ambient a
    have bindIte {α β : Type} (c : Prop) [Decidable c]
        (a b : Leanux.M α) (f : α → Leanux.M β) :
        ((if c then a else b) >>= f) = (if c then a >>= f else b >>= f) := by
      split <;> rfl
    simp only [enqueuePerPeerRx, before, lift, liftWG_bind, bind_assoc]
    simp only [apply_ite, bindIte, liftWG_bind, liftWG_pure, invariant,
      ambientLift, bind_assoc, pure_bind]
  rw [factor]
  apply ProjectedAction.of_wp
  intro initial
  have hb : Hoare (liftWG before)
      (fun w => RetainsRouting initial (routingView w.wg))
      (fun _ w => RetainsRouting initial (routingView w.wg)) :=
    (sameView_liftWG (fun w => routingView w.wg) routingView before
      before_frame (fun _ _ _ h => h)).wp (RetainsRouting initial)
  unfold Hoare at hb
  have hir := RetainsRoutingCall.wp hi initial
  have hp := fun pid => RetainsRoutingCall.wp ((peerPut_retainsRouting (some pid)).liftWG) initial
  mvcgen [hb, hir, hp]
  subst initial
  exact RetainsRouting.refl _

private theorem decryptPoll_routing : SameView routingView RxRing.pollSource := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => (fun t => t = s) (routingView w)) (fun _ w => (fun t => t = s) (routingView w)) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hm := fun ring => (modifyDev_routing (fun d => {d with decryptQueue := ring}) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, RxRing.pollSource, hm, getDev, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView]

theorem decryptStep_routing (softirq irq : Leanux.M Unit)
    (hs : ProductRetainsRoutingCall softirq) (hi : ProductRetainsRoutingCall irq) :
    ProductRetainsRoutingCall (decryptStep softirq irq) := by
  rw [← RxRing.stepSource_eq]
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg)) (fun _ w => RetainsRouting s (routingView w.wg)) := productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  let P := RetainsRouting s
  have native {α : Type} (a : WG.M α) (ha : SameView routingView a) :=
    (sameView_liftWG (fun w => routingView w.wg) routingView a ha (fun _ _ _ h => h)).wp P
  have nativeSkb {α : Type} (a : SkbM α) : SameView routingView (liftSkb a) := by
    intro initial
    apply hoare_liftSkb a
    intro w d store hi hd
    unfold routingView at hi ⊢
    simpa only [hd, Option.map_some, routingState] using hi
  have skb {α : Type} (a : SkbM α) := native (liftSkb a) (nativeSkb a)
  have hsoft := RetainsRoutingCall.wp hs s
  have hp : Hoare (liftWG RxRing.pollSource)
      (fun w => P (routingView w.wg)) (fun _ w => P (routingView w.wg)) :=
    native _ decryptPoll_routing
  unfold Hoare at hp
  have hd := fun pkt => native _ (decryptPacket_routing pkt)
  have hq := fun id state => RetainsRoutingCall.wp (enqueuePerPeerRx_routing irq hi id state) s
  mvcgen [getRxSkb, setRxSkb, freeRxSkb, skb, liftM, -Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, RxRing.stepSource, hsoft, hp, hd, hq, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem decryptIter_routing (softirq irq : Leanux.M Unit) (need : Leanux.M Bool)
    (hs : ProductRetainsRoutingCall softirq) (hi : ProductRetainsRoutingCall irq) (hn : ProductRetainsRoutingCall need) :
    ProductRetainsRoutingCall (decryptIter softirq irq need) := by
  apply workerIter_routing _ _ _ _ (decryptStep_routing softirq irq hs hi)
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => RetainsRouting s (routingView w.wg)) (fun _ w => RetainsRouting s (routingView w.wg)) := productAmbient_spec a _ (fun _ _ h => h)
  unfold Hoare at ambient
  have hneed := RetainsRoutingCall.wp hn s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, branch, branchCmp, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported, hneed, branch]
  subst s
  exact RetainsRouting.refl _

end Leanux.Proofs.WG.AllowedIps
