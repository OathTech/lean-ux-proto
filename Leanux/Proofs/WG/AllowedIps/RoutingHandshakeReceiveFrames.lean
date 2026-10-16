import Leanux.Proofs.WG.AllowedIps.RoutingNoiseReceiveFrames
import Leanux.Proofs.WG.Cookies.Gate

/-! Complete original handshake receive and its actual worker iteration are
silent for routing. Normal endpoints may delete resident peers; missing stores,
malformed packets and record failures retain their original Stop behavior. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem setPeerEndpointFromSkb_routing (pid : PeerId) (src : SkbSource) :
    SameView routingView (setPeerEndpointFromSkb pid src) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => routingView w = s) (fun _ w => routingView w = s) :=
    hoare_liftAmbient a _
  unfold Hoare at ambient
  have he := (routing_kernel _ (endpointFromSkb_sameWGStore src)).wp (fun t => t = s)
  have hs := fun e => (setPeerEndpoint_routing pid e).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hiddenAlloc, hiddenClock64, branch, branchCmp, invariant, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, setPeerEndpointFromSkb, he, hs, branch, invariant]

theorem sendBufferAsReplyToSkb_routing (src : SkbSource) (bytes : List UInt8) :
    SameView routingView (sendBufferAsReplyToSkb src bytes) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => routingView w = s) (fun _ w => routingView w = s) :=
    hoare_liftAmbient a _
  unfold Hoare at ambient
  have he := (routing_kernel _ (endpointFromSkb_sameWGStore src)).wp (fun t => t = s)
  have h4 := fun e => (send4_routing e none bytes 0 false).wp (fun t => t = s)
  have h6 := fun e => (send6_routing e none bytes 0 false).wp (fun t => t = s)
  have hd (α : Type) := discard_view_spec (m := AmbientM) routingView (α := α) (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hiddenAlloc, hiddenClock64, branch, branchCmp, invariant, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, sendBufferAsReplyToSkb, he, h4, h6, hd, branch, invariant]

theorem sendHandshakeCookie_routing (msg : List UInt8) (src : SkbSource) :
    SameView routingView (sendHandshakeCookie msg src) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => routingView w = s) (fun _ w => routingView w = s) :=
    hoare_liftAmbient a _
  unfold Hoare at ambient
  have hc := fun i mac => (cookie_routing_native _ (cookieMessageCreate_sameCookie i src mac)).wp (fun t => t = s)
  have hs := fun bytes => (sendBufferAsReplyToSkb_routing src bytes).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hiddenAlloc, hiddenClock64, branch, branchCmp, invariant, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, sendHandshakeCookie, hc, hs]

private def handshakeSwitch (msg : List UInt8) (src : SkbSource) (needsCookie : Bool) : WG.M Unit := do
  let t := messageType msg
  let peer ← do
    if ← branch .hsSwitchInitiation (t == MESSAGE_HANDSHAKE_INITIATION) then
      if ← branch .hsInitNeedsCookie needsCookie then
        sendHandshakeCookie msg src
        return
      let peer ← consumeInitiation msg
      if ← branch .hsInitNoPeer peer.isNone then return
      let some pid := peer | invariant "unreachable"
      setPeerEndpointFromSkb pid src
      sendHandshakeResponse pid
      pure peer
    else if ← branch .hsSwitchResponse (t == MESSAGE_HANDSHAKE_RESPONSE) then
      if ← branch .hsRespNeedsCookie needsCookie then
        sendHandshakeCookie msg src
        return
      let peer ← consumeResponse msg
      if ← branch .hsRespNoPeer peer.isNone then return
      let some pid := peer | invariant "unreachable"
      setPeerEndpointFromSkb pid src
      if ← branch .hsRespSessionBegun (← beginSession pid) then
        timersSessionDerived pid
        timersHandshakeComplete pid
        -- either sends the staged packets or stages a keepalive and sends it
        sendKeepalive pid
      pure peer
    else pure none
  if ← branch .hsWrongPacket peer.isNone then invariant "a wrong type of packet in the handshake queue"
  let some pid := peer | invariant "unreachable"
  -- update_rx_stats: peer->rx_bytes (wg0's own rx counters,
  -- dev_sw_netstats_rx_add, are not tracked: nothing reads them on the
  -- modeled paths)
  let p ← getPeer pid
  setPeer pid { p with rxBytes := p.rxBytes + msg.length }
  -- update_rx_stats (receive.c:198): the device tstats too (W5, 2.6)
  modifyDev fun d => { d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + msg.length }
  timersAnyAuthenticatedPacketReceived pid
  timersTraversal pid
  peerPut peer

private def handshakeAfterMac (msg : List UInt8) (src : SkbSource) (underLoad : Bool) (macState : MacState) : WG.M Unit := do
  -- packet_needs_cookie (receive.c:123-132):
  -- `(under_load && mac == WITH_COOKIE) || (!under_load && mac == NO_COOKIE)`
  let proceed ← WG.orM (WG.andM (branch .hsLoadedOperand underLoad) (branch .hsLoadedCookieOk (macState == .withCookie)))
                    (WG.andM (branch .hsNotLoaded (!underLoad)) (branch .hsMacNoCookie (macState == .noCookie)))
  let needsCookie ← do
    if proceed then pure false
    -- `else if (under_load && mac == VALID_MAC_BUT_NO_COOKIE)`
    else if ← WG.andM (branch .hsNeedsCookieLoaded underLoad) (branch .hsNeedsCookieMac (macState == .noCookie)) then
      pure true
    else return   -- invalid MAC: the packet is dropped
  handshakeSwitch msg src needsCookie

private theorem handshakeAfterMac_eq (msg : List UInt8) (src : SkbSource) (loaded : Bool) (mac : MacState) :
    handshakeAfterMac msg src loaded mac = Cookies.afterMac msg src loaded mac := rfl

private theorem handshakeSwitch_routing (msg : List UInt8) (src : SkbSource) (needsCookie : Bool) :
    RetainsRoutingCall (handshakeSwitch msg src needsCookie) := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => RetainsRouting s (routingView w))
        (fun _ w => RetainsRouting s (routingView w)) :=
    hoare_liftAmbient a _
  unfold Hoare at ambient
  let P := RetainsRouting s
  have hg := fun pid => routing_getPeer P pid
  have hs := fun pid p => routing_setPeer P pid p
  have hu := fun peer => RetainsRoutingCall.wp (peerPut_retainsRouting peer) s
  have hsc := (sendHandshakeCookie_routing msg src).wp P
  have hi := RetainsRoutingCall.wp (consumeInitiation_routing msg) s
  have hr := RetainsRoutingCall.wp (consumeResponse_routing msg) s
  have he := fun pid => (setPeerEndpointFromSkb_routing pid src).wp P
  have hsend := fun pid => (sendHandshakeResponse_routing pid).wp P
  have hbegin := fun pid => (beginSession_routing pid).wp P
  have hd := fun pid => (timersSessionDerived_routing pid).wp P
  have hcomplete := fun pid => (timersHandshakeComplete_routing pid .walltimeLastHandshake).wp P
  have hk := fun pid => RetainsRoutingCall.wp (sendKeepalive_routing pid) s
  have hrecv := fun pid => (timersAnyAuthenticatedPacketReceived_routing pid).wp P
  have ht := fun pid => (timersTraversal_routing pid).wp P
  have hm := (modifyDev_routing (fun d => {d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + msg.length})
    (fun _ => rfl)).wp P
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hiddenAlloc, hiddenClock64, branch, branchCmp, invariant, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, handshakeSwitch, hg, hs, hu, hsc, hi, hr,
    he, hsend, hbegin, hd, hcomplete, hk, hrecv, ht, hm, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try simp_all
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

private theorem handshakeAfterMac_routing (msg : List UInt8) (src : SkbSource) (underLoad : Bool) (macState : MacState) :
    RetainsRoutingCall (Cookies.afterMac msg src underLoad macState) := by
  rw [← handshakeAfterMac_eq]
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => RetainsRouting s (routingView w))
        (fun _ w => RetainsRouting s (routingView w)) :=
    hoare_liftAmbient a _
  unfold Hoare at ambient
  let P := RetainsRouting s
  have hs := fun b => RetainsRoutingCall.wp (handshakeSwitch_routing msg src b) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hiddenAlloc, hiddenClock64, branch, branchCmp, invariant, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, handshakeAfterMac, hs, WG.andM, WG.orM]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try simp_all
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem receiveHandshakePacket_routing (msg : List UInt8) (src : SkbSource) :
    RetainsRoutingCall (receiveHandshakePacket msg src) := by
  rw [Cookies.receive_factor]
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => RetainsRouting s (routingView w))
        (fun _ w => RetainsRouting s (routingView w)) :=
    hoare_liftAmbient a _
  unfold Hoare at ambient
  let P := RetainsRouting s
  have hc := RetainsRoutingCall.wp (cookieMessageConsume_routing msg) s
  have hl := (routing_kernel _ Cookies.loadPhase_sameStore).wp P
  have hv := fun loaded => (cookie_routing_native _ (cookieValidatePacket_sameCookie msg src loaded)).wp P
  have ha := fun loaded mac => RetainsRoutingCall.wp (handshakeAfterMac_routing msg src loaded mac) s
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hiddenAlloc, hiddenClock64, branch, branchCmp, invariant, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, hc, hl, hv, ha]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem receiveStep_routing : RetainsRoutingCall receiveStep := by
  apply ProjectedAction.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => RetainsRouting s (routingView w))
        (fun _ w => RetainsRouting s (routingView w)) :=
    hoare_liftAmbient a _
  unfold Hoare at ambient
  let P := RetainsRouting s
  have hr := fun msg src => RetainsRoutingCall.wp (receiveHandshakePacket_routing msg src) s
  have hq := fun ring => (modifyDev_routing (fun d => {d with handshakeQueue := ring})
    (fun _ => rfl)).wp P
  have hc := (modifyDev_routing (fun d => {d with handshakeQueueLen := d.handshakeQueueLen - 1})
    (fun _ => rfl)).wp P
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hiddenAlloc, hiddenClock64, branch, branchCmp, invariant, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, receiveStep, hr, hq, hc, getDev, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try simp_all
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem actualReceiveIter_routing :
    ProductRetainsRoutingCall
      (workerIter .receiveWorker none (liftWG receiveStep) (Env.condResched .receiveWorker)) :=
  workerIter_routing _ _ _ _ receiveStep_routing.liftWG
    (ProjectedRetainsRoutingCall.of_same
      ((Framing.condResched_sameKernel .receiveWorker).of_factor
        (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
        (fun w : World => routingView w.wg) (fun _ => rfl)))

end Leanux.Proofs.WG.AllowedIps
