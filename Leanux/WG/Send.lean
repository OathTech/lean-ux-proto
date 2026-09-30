import Leanux.WG.Peer

/-!
# drivers/net/wireguard/send.c — staging and handshake queueing, before any session

No session keypair exists in stage B1: `current_keypair` is NULL, so staged
packets stay staged and a handshake initiation is queued.

The handshake worker (`wg_packet_handshake_send_worker`, send.c:21-53) runs in
a kworker, outside the operation's KCOV coverage, at a time the trace does not
determine. The mirror models it as a contract, applied when `wg_observe` has
waited for it (`runHandshakeWorkers`), without reporting decisions. Until then,
every path that reads what the worker changes is `unsupported`
(`requireNotPending`).
-/

namespace Leanux.WG
open Leanux

def MAX_STAGED_PACKETS : Nat := 128

/-- wg_packet_send_queued_handshake_initiation (send.c:55-83). The pending
    check comes first: once queued, `queue_work` and `last_sent_handshake`
    depend on the worker's timing. -/
def sendQueuedHandshakeInitiation (pid : PeerId) (isRetry : Bool) : M Unit := do
  requireNotPending pid "queueing a handshake"
  -- `peer->timer_handshake_attempts = 0` (timers are cut points)
  _ ← branch .queuedNotRetry !isRetry
  let p ← getPeer pid
  -- `!wg_birthdate_has_expired(last_sent_handshake, REKEY_TIMEOUT) || is_dead`
  if ← branch .queuedNotExpired !p.lastSentExpired then return
  if ← branch .queuedDead p.isDead then return
  peerGet pid
  -- `!queue_work(...)`: false iff the work is still queued (queued earlier in
  -- this call; requireNotPending excludes every other pending case)
  if ← branch .queuedAlreadyQueued p.handshakePending then
    peerPut (some pid)
    return
  setPeer pid { (← getPeer pid) with handshakePending := true }
  modify fun w => { w with queuedThisCall := pid :: w.queuedThisCall }

/-- wg_noise_keypair_get (noise.c:142-149) of the NULL `current_keypair`. -/
def keypairGetCurrent : M Unit := do
  -- `unlikely(!keypair || ...)`: `!keypair` decides
  _ ← branch .keypairGetNull true

/-- wg_packet_send_staged_packets (send.c:342-414) with no session. -/
def sendStagedPackets (pid : PeerId) : M Unit := do
  let p ← getPeer pid
  -- skb_queue_splice_init onto the local list, then
  if ← branch .stagedEmpty (p.staged == 0) then return
  keypairGetCurrent
  if !(← branch .stagedNoKeypair true) then unsupported "a session keypair"
  keypairPutNull   -- out_nokey: wg_noise_keypair_put(NULL, false)
  for _ in [0:p.staged] do _ ← branch .stagedOrphanWalk true   -- skb_orphan
  _ ← branch .stagedOrphanWalk false
  -- skb_queue_splice: the packets go back on the staged queue
  sendQueuedHandshakeInitiation pid false

/-- wg_packet_send_keepalive (send.c:221-240): a keepalive is staged only
    when nothing else is. -/
def sendKeepalive (pid : PeerId) : M Unit := do
  let p ← getPeer pid
  if ← branch .keepaliveStagedEmpty (p.staged == 0) then
    if ← branch .keepaliveNoMem !(← envOk .allocSkb) then return
    setPeer pid { p with staged := p.staged + 1 }
  sendStagedPackets pid

/-- Whether an endpoint is one of the fixture's listeners. -/
def listenerFamily (e : Endpoint) : Option Nat :=
  if e.port != LISTEN_PORT then none
  else if e.family == AF_INET && e.addr == 0x7f000001 then some 4
  else if e.family == AF_INET6 && e.addr == 1 then some 6
  else none

/-- The handshake worker's contract, for each peer whose work is queued,
    once `wg_observe` has waited for it: `last_sent_handshake` becomes
    current, and an initiation (148 bytes) is sent to the endpoint iff
    `wg_noise_handshake_create_initiation` succeeds, which is iff the device
    has an identity and the precomputed static-static is nonzero (with a
    low-order remote key the ephemeral DH is zero too). It is sent if the peer
    has an endpoint (else `wg_socket_send_skb_to_peer` fails with
    -EAFNOSUPPORT), and a sent initiation adds to `tx_bytes`. The worker drops
    the reference the queueing took. Endpoints other than loopback would route
    back into wg0 from the worker; they are outside the domain. -/
def runHandshakeWorkers : M Unit := do
  let d ← getDev
  for (pid, p) in d.peers.toList do
    if !p.handshakePending then continue
    let created := d.staticIdentity.hasIdentity && p.precomputedStaticStatic != List.replicate 32 0
    -- wg_socket_send_skb_to_peer: with no endpoint, -EAFNOSUPPORT and no bytes
    let sent := created && p.endpoint.isSome
    if let some e := p.endpoint then
      let loopback := (e.family == AF_INET && e.addr / 2 ^ 24 == 127) || (e.family == AF_INET6 && e.addr == 1)
      if created && !loopback then unsupported "a handshake sent to a non-loopback endpoint"
    if p.refcount < 2 then invariant "the worker's reference is missing"
    setPeer pid { p with handshakePending := false, lastSentExpired := false, refcount := p.refcount - 1,
                         txBytes := p.txBytes + (if sent then MESSAGE_HANDSHAKE_INITIATION_LEN else 0) }
    if sent then
      let some e := p.endpoint | invariant "unreachable"
      match listenerFamily e with
      | some 4 => modifyK fun k => { k with listeners := { k.listeners with v4 := k.listeners.v4 ++ [MESSAGE_HANDSHAKE_INITIATION_LEN] } }
      | some _ => modifyK fun k => { k with listeners := { k.listeners with v6 := k.listeners.v6 ++ [MESSAGE_HANDSHAKE_INITIATION_LEN] } }
      | none => pure ()

end Leanux.WG
