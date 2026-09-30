import Leanux.WG.Peer

/-!
# drivers/net/wireguard/send.c — staging and handshake queueing, before any session

No session keypair exists in stage B1: `current_keypair` is NULL, so staged
packets stay staged and a handshake initiation is queued.

The handshake worker (`wg_packet_handshake_send_worker`, send.c:21-53) runs in
a kworker at a time the trace does not determine. It is not mirrored here; the
environment model (`Leanux/Env.lean`) applies its contract when `wg_observe`
has waited for it. Until then, every path that reads what the worker changes
is `unsupported` (`requireNotPending`).
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

end Leanux.WG
