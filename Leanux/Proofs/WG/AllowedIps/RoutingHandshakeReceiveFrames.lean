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
  have endpoint : SameView routingView (endpointFromSkb src) := routing_kernel _ (endpointFromSkb_sameWGStore src)
  routing_handshake_source [setPeerEndpointFromSkb] using [endpoint, setPeerEndpoint_routing]

theorem sendBufferAsReplyToSkb_routing (src : SkbSource) (bytes : List UInt8) :
    SameView routingView (sendBufferAsReplyToSkb src bytes) := by
  have endpoint : SameView routingView (endpointFromSkb src) := routing_kernel _ (endpointFromSkb_sameWGStore src)
  routing_handshake_source [sendBufferAsReplyToSkb] using [endpoint, send4_routing, send6_routing]

theorem sendHandshakeCookie_routing (msg : List UInt8) (src : SkbSource) :
    SameView routingView (sendHandshakeCookie msg src) := by
  have cookie := fun i mac => show SameView routingView _ from
    cookie_routing_native _ (cookieMessageCreate_sameCookie i src mac)
  routing_handshake_source [sendHandshakeCookie] using [cookie, sendBufferAsReplyToSkb_routing]

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
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have cookie : Preserves P (sendHandshakeCookie msg src) := (sendHandshakeCookie_routing msg src).wp Q
  have initiation : Preserves P (consumeInitiation msg) := RetainsRoutingCall.wp (consumeInitiation_routing msg) s
  have response : Preserves P (consumeResponse msg) := RetainsRoutingCall.wp (consumeResponse_routing msg) s
  have endpoint (pid : PeerId) : Preserves P (setPeerEndpointFromSkb pid src) := (setPeerEndpointFromSkb_routing pid src).wp Q
  have send (pid : PeerId) : Preserves P (sendHandshakeResponse pid) := (sendHandshakeResponse_routing pid).wp Q
  have begun (pid : PeerId) : Preserves P (beginSession pid) := (beginSession_routing pid).wp Q
  have derived (pid : PeerId) : Preserves P (timersSessionDerived pid) := (timersSessionDerived_routing pid).wp Q
  have complete (pid : PeerId) : Preserves P (timersHandshakeComplete pid .walltimeLastHandshake) :=
    (timersHandshakeComplete_routing pid .walltimeLastHandshake).wp Q
  have keep (pid : PeerId) : Preserves P (sendKeepalive pid) := RetainsRoutingCall.wp (sendKeepalive_routing pid) s
  have authenticated (pid : PeerId) : Preserves P (timersAnyAuthenticatedPacketReceived pid) :=
    (timersAnyAuthenticatedPacketReceived_routing pid).wp Q
  have traversal (pid : PeerId) : Preserves P (timersTraversal pid) := (timersTraversal_routing pid).wp Q
  have put (pid : Option PeerId) : Preserves P (peerPut pid) := RetainsRoutingCall.wp (peerPut_retainsRouting pid) s
  have stats : Preserves P (modifyDev fun d => {d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + msg.length}) :=
    (modifyDev_routing (fun d => {d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + msg.length}) (fun _ => rfl)).wp Q
  let received (pid : PeerId) : WG.M Unit := do
    let p ← getPeer pid
    setPeer pid {p with rxBytes := p.rxBytes + msg.length}
  have receivedFrame (pid : PeerId) : Preserves P (received pid) :=
    (modifyPeer_routing pid (fun p => {p with rxBytes := p.rxBytes + msg.length}) (fun _ => rfl)).wp Q
  have source : handshakeSwitch msg src needsCookie = (do
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
      received pid
      -- update_rx_stats (receive.c:198): the device tstats too (W5, 2.6)
      modifyDev fun d => { d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + msg.length }
      timersAnyAuthenticatedPacketReceived pid
      timersTraversal pid
      peerPut peer
    ) := by
    simp only [handshakeSwitch, received, bind_assoc]
  have main : Preserves P (handshakeSwitch msg src needsCookie) := by
    rw [source]
    routing_tx_source [] using [cookie, initiation, response, endpoint, send, begun, derived,
      complete, keep, authenticated, traversal, put, stats, receivedFrame, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

private theorem handshakeAfterMac_routing (msg : List UInt8) (src : SkbSource) (underLoad : Bool) (macState : MacState) :
    RetainsRoutingCall (Cookies.afterMac msg src underLoad macState) := by
  rw [← handshakeAfterMac_eq]
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have switch (needs : Bool) : Preserves P (handshakeSwitch msg src needs) :=
    RetainsRoutingCall.wp (handshakeSwitch_routing msg src needs) s
  have main : Preserves P (handshakeAfterMac msg src underLoad macState) := by
    routing_tx_source [handshakeAfterMac] using [switch, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem receiveHandshakePacket_routing (msg : List UInt8) (src : SkbSource) :
    RetainsRoutingCall (receiveHandshakePacket msg src) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have cookie : Preserves P (cookieMessageConsume msg) := RetainsRoutingCall.wp (cookieMessageConsume_routing msg) s
  have load : Preserves P Cookies.loadPhase := (routing_kernel _ Cookies.loadPhase_sameStore).wp Q
  have validate (loaded : Bool) : Preserves P (cookieValidatePacket msg src loaded) :=
    (cookie_routing_native _ (cookieValidatePacket_sameCookie msg src loaded)).wp Q
  have after (loaded : Bool) (mac : MacState) : Preserves P (Cookies.afterMac msg src loaded mac) :=
    RetainsRoutingCall.wp (handshakeAfterMac_routing msg src loaded mac) s
  have main : Preserves P (receiveHandshakePacket msg src) := by
    rw [Cookies.receive_factor]
    routing_tx_source [] using [cookie, load, validate, after, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem receiveStep_routing : RetainsRoutingCall receiveStep := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have receive (msg : List UInt8) (src : SkbSource) : Preserves P (receiveHandshakePacket msg src) :=
    RetainsRoutingCall.wp (receiveHandshakePacket_routing msg src) s
  have queue (ring : PtrRing (List UInt8 × SkbSource)) : Preserves P (modifyDev fun d => {d with handshakeQueue := ring}) :=
    (modifyDev_routing (fun d => {d with handshakeQueue := ring}) (fun _ => rfl)).wp Q
  have count : Preserves P (modifyDev fun d => {d with handshakeQueueLen := d.handshakeQueueLen - 1}) :=
    (modifyDev_routing (fun d => {d with handshakeQueueLen := d.handshakeQueueLen - 1}) (fun _ => rfl)).wp Q
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have main : Preserves P receiveStep := by
    routing_tx_source [receiveStep] using [receive, queue, count, device, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem actualReceiveIter_routing :
    ProductRetainsRoutingCall
      (workerIter .receiveWorker none (liftWG receiveStep) (Env.condResched .receiveWorker)) :=
  workerIter_routing _ _ _ _ receiveStep_routing.liftWG
    (ProjectedRetainsRoutingCall.of_same
      ((Framing.condResched_sameKernel .receiveWorker).of_factor
        (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
        (fun w : World => routingView w.wg) (fun _ => rfl)))

end Leanux.Proofs.WG.AllowedIps
