import Leanux.Proofs.WG.Roaming.ResponseCallSource
import Leanux.Proofs.WG.TimerDiscipline.ObservationProductSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

/-- The strict actual load/MAC prefix, before every admission decision and
before either handshake consumer. The cookie arm is excluded by the source theorem. -/
def rateLimitPrefix (msg : List UInt8) (src : SkbSource) : WG.M (Bool × MacState) := do
  _ ← branch .hsCookie false
  let loaded ← responseLoad
  let mac ← cookieValidatePacket msg src loaded
  return (loaded, mac)

/-- The unchanged receive body after its actual MAC verdict. -/
def rateLimitSuffix (msg : List UInt8) (src : SkbSource) (input : Bool × MacState) : WG.M Unit := do
  let (underLoad, macState) := input
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

/-- Exact original non-cookie receiver, including every prefix and suffix Stop. -/
theorem receiveHandshakePacket_rateLimit_factor (msg : List UInt8) (src : SkbSource)
    (noncookie : messageType msg ≠ MESSAGE_HANDSHAKE_COOKIE) :
    receiveHandshakePacket msg src = (rateLimitPrefix msg src >>= rateLimitSuffix msg src) := by
  rw [← Index.receivePacket_source]
  have branch_native : (branch .hsCookie false : WG.M Bool) = (do
      (monadLift (modify fun a : Ambient => {a with steps := a.steps.push {
        decision := .hsCookie, outcome := false, netRx := a.netRxSection}} : AmbientM Unit) : WG.M Unit)
      pure false) := rfl
  simp only [Index.receivePacketSource, beq_eq_false_iff_ne.mpr noncookie,
    branch_native, bind_assoc, pure_bind, Bool.false_eq_true, ite_false]
  rw [← responseLoad_source]
  simp only [rateLimitPrefix, branch_native, bind_assoc, pure_bind]
  rfl

/-- The inspection preserves actual prefix errors, then executes the original
receiver. No successful-prefix or readiness premise is supplied. -/
def observedRateLimitHandshake (msg : List UInt8) (src : SkbSource) :
    Leanux.M (Campaign2.Product.Outcome (Bool × MacState) × Unit) :=
  TimerDiscipline.observed (liftWG (receiveHandshakePacket msg src))
    (liftWG (rateLimitPrefix msg src))

theorem observedRateLimitHandshake_erase (msg : List UInt8) (src : SkbSource) :
    (do let result ← observedRateLimitHandshake msg src; pure result.2) =
      liftWG (receiveHandshakePacket msg src) :=
  TimerDiscipline.observed_erase _ _

end Leanux.Proofs.WG.Roaming
