import Leanux.WG.Receive

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Original load test and historical-load decay, passing the resulting flag
to the continuation at the MAC-validation boundary. -/
def receiveLoadThen (next : Bool → WG.M Unit) : WG.M Unit := do
  -- `under_load = handshake_queue_len >= MAX_QUEUED_INCOMING_HANDSHAKES / 8`
  -- (receive.c:112): the counter, which a `wg_flood`'s batch has filled before
  -- the worker runs (E-B v2, the queue-depth design).
  let mut underLoad := false
  -- the compare's operands: the counter (an int) against the constant 512,
  -- compiled `> 511`, which the check's `ge` shift absorbs (declared 2026-10-14)
  let queueLen := (← getDev).handshakeQueueLen
  if ← branchCmp .hsUnderLoad (queueLen ≥ MAX_QUEUED_INCOMING_HANDSHAKES / 8)
        (Int.ofNat queueLen) (Int.ofNat (MAX_QUEUED_INCOMING_HANDSHAKES / 8)) then
    -- `last_under_load = ktime_get_coarse_boottime_ns()` (receive.c:115)
    let now ← hiddenClock64 .underLoadNow
    modify fun w => { w with lastUnderLoad := some now }
    underLoad := true
  -- `else if (last_under_load)`: the function-static (receive.c:100), nonzero
  -- after a flood this trace ran (every normal trace keeps it `none`, §4.2).
  else if ← branch .hsWasUnderLoad (← get).lastUnderLoad.isSome then
    let some last := (← get).lastUnderLoad | invariant "unreachable"
    -- `under_load = !wg_birthdate_has_expired(last_under_load, 1)` (receive.c:117),
    -- the recorded clock against the saved time; `if (!under_load)
    -- last_under_load = 0` (receive.c:118-119): the decay's reset
    let (expired, lhs, now) ← birthdateTest last 1
    underLoad := !expired
    -- the age test's operands are recorded at receive.c:117 (`Decision.comparison`'s site)
    if ← branchCmp .hsDecayExpired expired lhs now then
      modify fun w => { w with lastUnderLoad := none }
  next underLoad

/-- Original packet body after the load test; early returns remain local to the
whole packet body, including the cookie-response and failed-consumption paths. -/
def receivePacketBody (msg : List UInt8) (src : SkbSource) (underLoad : Bool) : WG.M Unit := do
  let macState ← cookieValidatePacket msg src underLoad
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


def receivePacketSource (msg : List UInt8) (src : SkbSource) : WG.M Unit := do
  if ← branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE) then
    cookieMessageConsume msg
    return
  receiveLoadThen (receivePacketBody msg src)

/-- Exact equality of computations, including stopped runs and early returns. -/
theorem receivePacket_source (msg : List UInt8) (src : SkbSource) :
    receivePacketSource msg src = receiveHandshakePacket msg src := by
  rfl

end Leanux.Proofs.WG.Index
