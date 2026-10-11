import Leanux.WG.Data

/-!
# drivers/net/wireguard/timers.c — the timer callbacks (D3)

The five callbacks `call_timer_fn` runs in `TIMER_SOFTIRQ`
(docs/2026-10-05-d3-timers.md, sections 2.1 and 5.2), decision for decision.
Each is entered with its own timer already detached (`expire_timers`,
timer.c:1828-1829): the environment clears the timer before the call
(`Env.fireTimer`). None sends on the wire itself: each queues work (the
handshake send worker, the clear work, or through `wg_packet_create_data`
the encrypt worker), or arms and deletes timers. The clear work itself,
`wg_queued_expired_zero_key_material`, is in `Keypair.lean` (peer removal's
`flush_work` runs it too).

The arm sites, `mod_peer_timer` and the timers' delays are in
`Handshake.lean`; `armTimer` and `delTimer` in `State.lean`.
-/

namespace Leanux.WG
open Leanux

/-- `MAX_TIMER_HANDSHAKES` (messages.h:50): `90 / REKEY_TIMEOUT`. -/
def MAX_TIMER_HANDSHAKES : Nat := 90 / REKEY_TIMEOUT

/-- wg_expired_retransmit_handshake (timers.c:41-77). -/
def expiredRetransmitHandshake (pid : PeerId) : M Unit := do
  if ← branch .retransmitGiveUp ((← getPeer pid).timerHandshakeAttempts > MAX_TIMER_HANDSHAKES) then
    delTimer pid .sendKeepalive
    -- we drop all packets without a keypair and don't try again
    purgeStagedPackets pid
    -- a timer for destroying any residue of a partial exchange
    if ← branch .retransmitZeroKeyNotPending !((← getPeer pid).timerPending .zeroKeyMaterial) then
      discard <| modPeerTimer pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS
  else
    let p ← getPeer pid
    setPeer pid { p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1 }
    clearPeerEndpointSrc pid
    sendQueuedHandshakeInitiation pid true

/-- wg_expired_send_keepalive (timers.c:79-89). The re-arm is short-lived on
    the modeled paths: the keepalive's tx worker deletes it
    (`timersAnyAuthenticatedPacketSent`). -/
def expiredSendKeepalive (pid : PeerId) : M Unit := do
  sendKeepalive pid
  if ← branch .keepaliveNeedAnother (← getPeer pid).timerNeedAnotherKeepalive then
    setPeer pid { (← getPeer pid) with timerNeedAnotherKeepalive := false }
    discard <| modPeerTimer pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS

/-- wg_expired_new_handshake (timers.c:91-103). -/
def expiredNewHandshake (pid : PeerId) : M Unit := do
  clearPeerEndpointSrc pid
  sendQueuedHandshakeInitiation pid false

/-- wg_expired_zero_key_material (timers.c:105-120): the clear work queued
    on `handshake_send_wq` with a peer reference; `queue_work` of work that
    is still queued fails, and the extra reference is dropped. -/
def expiredZeroKeyMaterial (pid : PeerId) : M Unit := do
  if ← branch .zeroKeyAlive !(← getPeer pid).isDead then
    peerGet pid
    if ← branch .zeroKeyAlreadyQueued ((← getDev).clearWorkQueue.contains pid) then
      peerPut (some pid)
    else
      recordQueued .clearPeerWorker pid   -- queue_work's record (dispatch order)
      modifyDev fun d => { d with clearWorkQueue := d.clearWorkQueue ++ [pid] }

/-- wg_expired_send_persistent_keepalive (timers.c:135-142). -/
def expiredSendPersistentKeepalive (pid : PeerId) : M Unit := do
  if ← branch .persistentKeepaliveInterval ((← getPeer pid).persistentKeepaliveInterval != 0) then
    sendKeepalive pid

/-- The callback of a timer (`timer_setup` in `wg_timers_init`,
    timers.c:219-233). -/
def timerCallback (pid : PeerId) : PeerTimer → M Unit
  | .retransmitHandshake => expiredRetransmitHandshake pid
  | .sendKeepalive => expiredSendKeepalive pid
  | .newHandshake => expiredNewHandshake pid
  | .zeroKeyMaterial => expiredZeroKeyMaterial pid
  | .persistentKeepalive => expiredSendPersistentKeepalive pid

end Leanux.WG
