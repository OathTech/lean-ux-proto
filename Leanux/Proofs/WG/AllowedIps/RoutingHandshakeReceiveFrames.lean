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
  have he := (routing_kernel _ (endpointFromSkb_sameKernel src)).wp (fun t => t = s)
  have hs := fun e => (setPeerEndpoint_routing pid e).wp (fun t => t = s)
  mvcgen [setPeerEndpointFromSkb, he, hs, branch, invariant]

theorem sendBufferAsReplyToSkb_routing (src : SkbSource) (bytes : List UInt8) :
    SameView routingView (sendBufferAsReplyToSkb src bytes) := by
  apply SameView.of_wp
  intro s
  have ha := (routing_kernel _ (hiddenAlloc_sameKernel .replySkb)).wp (fun t => t = s)
  have he := (routing_kernel _ (endpointFromSkb_sameKernel src)).wp (fun t => t = s)
  have h4 := fun e => (send4_routing e none bytes 0 false).wp (fun t => t = s)
  have h6 := fun e => (send6_routing e none bytes 0 false).wp (fun t => t = s)
  have hd (α : Type) := discard_view_spec routingView (α := α) (fun t => t = s)
  mvcgen [sendBufferAsReplyToSkb, ha, he, h4, h6, hd, branch, invariant]

theorem sendHandshakeCookie_routing (msg : List UInt8) (src : SkbSource) :
    SameView routingView (sendHandshakeCookie msg src) := by
  apply SameView.of_wp
  intro s
  have hc := fun i mac => (cookie_routing _ (cookieMessageCreate_sameCookieKernel i src mac)).wp (fun t => t = s)
  have hs := fun bytes => (sendBufferAsReplyToSkb_routing src bytes).wp (fun t => t = s)
  mvcgen [sendHandshakeCookie, hc, hs]

private def handshakeSwitch (msg : List UInt8) (src : SkbSource) (needsCookie : Bool) : M Unit := do
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

private def handshakeAfterMac (msg : List UInt8) (src : SkbSource) (underLoad : Bool) (macState : MacState) : M Unit := do
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
  let P := RetainsRouting s
  have hg := fun pid => routing_getPeer P pid
  have hs := fun pid p => routing_setPeer P pid p
  have hu := fun peer => (peerPut_retainsRouting peer).wp s
  have hc := fun site => (routing_kernel _ (hiddenClock64_sameKernel site)).wp P
  have hcookie := (cookieMessageConsume_routing msg).wp s
  have ha := fun b n => (routing_kernel _ (birthdateTest_sameKernel b n)).wp P
  have hv := fun b => (cookie_routing _ (cookieValidatePacket_sameCookieKernel msg src b)).wp P
  have hsc := (sendHandshakeCookie_routing msg src).wp P
  have hi := (consumeInitiation_routing msg).wp s
  have hr := (consumeResponse_routing msg).wp s
  have he := fun pid => (setPeerEndpointFromSkb_routing pid src).wp P
  have hsend := fun pid => (sendHandshakeResponse_routing pid).wp P
  have hbegin := fun pid => (beginSession_routing pid).wp P
  have hd := fun pid => (timersSessionDerived_routing pid).wp P
  have hcomplete := fun pid => (timersHandshakeComplete_routing pid .walltimeLastHandshake).wp P
  have hk := fun pid => (sendKeepalive_routing pid).wp s
  have hrecv := fun pid => (timersAnyAuthenticatedPacketReceived_routing pid).wp P
  have ht := fun pid => (timersTraversal_routing pid).wp P
  have hm := (modifyDev_routing (fun d => {d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + msg.length})
    (fun _ => rfl)).wp P
  have hb := fun d b => (routing_kernel _ (sameKernel_branch d b)).wp P
  have hbc := fun d b x y => (routing_kernel _ (branchCmp_sameKernel d b x y)).wp P
  mvcgen [hb, hbc, handshakeSwitch, hg, hs, hu, hc, hsc, hi, hr,
    he, hsend, hbegin, hd, hcomplete, hk, hrecv, ht, hm, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, routingState]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

private theorem handshakeAfterMac_routing (msg : List UInt8) (src : SkbSource) (underLoad : Bool) (macState : MacState) :
    RetainsRoutingCall (Cookies.afterMac msg src underLoad macState) := by
  rw [← handshakeAfterMac_eq]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hs := fun b => (handshakeSwitch_routing msg src b).wp s
  have hb := fun d b => (routing_kernel _ (sameKernel_branch d b)).wp P
  mvcgen [hb, handshakeAfterMac, hs, WG.andM, WG.orM]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView, routingState]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem receiveHandshakePacket_routing (msg : List UInt8) (src : SkbSource) :
    RetainsRoutingCall (receiveHandshakePacket msg src) := by
  rw [Cookies.receive_factor]
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hc := (cookieMessageConsume_routing msg).wp s
  have hl := (routing_kernel _ Cookies.loadPhase_sameKernel).wp P
  have hv := fun loaded => (cookie_routing _ (cookieValidatePacket_sameCookieKernel msg src loaded)).wp P
  have ha := fun loaded mac => (handshakeAfterMac_routing msg src loaded mac).wp s
  have hb := fun d b => (routing_kernel _ (sameKernel_branch d b)).wp P
  mvcgen [hb, hc, hl, hv, ha]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem receiveStep_routing : RetainsRoutingCall receiveStep := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hr := fun msg src => (receiveHandshakePacket_routing msg src).wp s
  have hq := fun ring => (modifyDev_routing (fun d => {d with handshakeQueue := ring})
    (fun _ => rfl)).wp P
  have hc := (modifyDev_routing (fun d => {d with handshakeQueueLen := d.handshakeQueueLen - 1})
    (fun _ => rfl)).wp P
  mvcgen [receiveStep, hr, hq, hc, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [routingView]
  all_goals try subst s
  all_goals first | exact RetainsRouting.refl _ | assumption

theorem actualReceiveIter_routing :
    RetainsRoutingCall (workerIter .receiveWorker none receiveStep (Env.condResched .receiveWorker)) :=
  workerIter_routing _ _ _ _ receiveStep_routing
    (.of_same (routing_kernel _ (Framing.condResched_sameKernel .receiveWorker)))

end Leanux.Proofs.WG.AllowedIps
