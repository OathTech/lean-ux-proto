import Leanux.WG.Handshake

/-!
# drivers/net/wireguard/peer.c — peer removal (W3, docs/2026-10-06-w3-w12.md, Part I)

`wg_peer_remove` (peer.c:156-165) and `wg_peer_remove_all` (167-184) end in
`peer_remove_after_dead` (94-150), which flushes `handshake_send_wq` twice:
`flush_work(&peer->clear_peer_work)` inside `wg_timers_stop` (timers.c:242,
from peer.c:106) and `flush_workqueue(peer->device->handshake_send_wq)`
(peer.c:129). The pool's worker runs its worklist while the netlink task
waits at the barrier (workqueue.c:4232-4300, 3971-): `flush_work` waits for
everything queued before the clear work and the clear work, and runs nothing
when it is not pending (`start_flush_work`, 4186-4188); `flush_workqueue`
waits for every queued item. Each item's `process_one_work` section is
recorded inside this operation, and its start record names the unit it runs
(docs/2026-10-11-dispatch-order.md), so a flush drains the queues in the
order the records show. The design's merged FIFO (section I.4) is not
needed for that: the order is captured, not assumed.

The removed peer's own send worker runs after `peer_make_dead` set
`is_dead`: `wg_packet_send_handshake_initiation` (send.c:21-44) does not test
it, so the initiation is built, MAC'd and sent to the still-set endpoint and
the retransmit jitter is drawn (timers.c:186, before `mod_peer_timer`'s
guard), but the guard `netif_running && !is_dead` (timers.c:33-34) fails:
no timer is armed and no arm record is written. Another peer's work the same
flush drains arms its timers as usual. The staged keepalive that queued the
work is purged at the peer's release (`kref_release`, peer.c:217:
`tx_dropped` counts it, `peerPut`).

Out of the domain, fail-noisy (section I.8): work pending across system
calls at a remove (`requireNotPending` at the paths that read it, as
before), queued crypt work at a remove (the `packet_crypt_wq` flushes,
peer.c:116 and 118: W3b), and `wg_peer_remove_all` with queued work, which
no modeled call reaches in-syscall (the drain still runs it as the kernel
would, at the first peer's flush).
-/

namespace Leanux.WG
open Leanux

/-- A queued `transmit_handshake_work` of peer `pid` run by a flush, inline
    with its section records (the kworker's dispatch while this task waits):
    the item leaves the queue as `process_one_work` dequeues it and clears
    its PENDING bit, then `wg_packet_handshake_send_worker` runs. -/
def runFlushedSendWork (pid : PeerId) : M Unit := do
  modifyDev fun d => { d with sendWorkQueue := d.sendWorkQueue.erase pid }
  let p ← getPeer pid
  if !p.handshakePending then invariant "queued work without a pending flag"
  setPeer pid { p with handshakePending := false }
  _ ← hidden (.sectionStart .sendWorker)
  handshakeSendWorker pid
  _ ← hidden (.sectionStop .sendWorker)

/-- A queued `clear_peer_work` of peer `pid` run by a flush, likewise. -/
def runFlushedClearWork (pid : PeerId) : M Unit := do
  modifyDev fun d => { d with clearWorkQueue := d.clearWorkQueue.erase pid }
  _ ← hidden (.sectionStart .clearPeerWorker)
  queuedExpiredZeroKeyMaterial pid
  _ ← hidden (.sectionStop .clearPeerWorker)

/-- The items of `handshake_send_wq` a flush runs, in the order the dispatch
    records name them. `upTo = some pid`: `flush_work(&pid->clear_peer_work)`,
    which runs up to and including that clear work (the caller has checked it
    is pending); `none`: `flush_workqueue`, every queued item. With records, a
    queued item the flush must wait for but no section names is a hidden
    mismatch (Linux ran something else, or nothing); without records (the
    domain filter) the send items run oldest first, then the clear items. -/
def drainHandshakeSendWq (upTo : Option PeerId) : M Unit := do
  for _ in [0:4096] do
    let d ← getDev
    if d.sendWorkQueue.isEmpty && d.clearWorkQueue.isEmpty then return
    match ← peekUnit .sendWorker with
    | some u =>
      let pid ← resolveUnit .sendWorker u d.sendWorkQueue
      runFlushedSendWork pid   -- the flushed item runs here
    | none =>
      match ← peekUnit .clearPeerWorker with
      | some u =>
        let pid ← resolveUnit .clearPeerWorker u d.clearWorkQueue
        runFlushedClearWork pid
        if upTo == some pid then return
      | none =>
        if (← get).hidden.isSome then
          throw (.hidden s!"a flush of handshake_send_wq must run queued work ({d.sendWorkQueue.length} send, {d.clearWorkQueue.length} clear items), but no section names it")
        -- the domain filter's placeholder order
        match d.sendWorkQueue.head?, d.clearWorkQueue.head? with
        | some pid, _ => runFlushedSendWork pid
        | none, some pid =>
          runFlushedClearWork pid
          if upTo == some pid then return
        | none, none => return
  invariant "handshake_send_wq did not drain"

/-- wg_timers_stop (timers.c:235-243): `timer_delete_sync` of the five
    timers (none can be running: one CPU, and a softirq is not preempted by
    this task), then `flush_work(&peer->clear_peer_work)`: a queued clear
    work runs now, with whatever the pool's worklist holds before it, while
    this task waits at the barrier. Called by peer removal and by `wg_stop`
    (L). -/
def timersStop (pid : PeerId) : M Unit := do
  for t in PeerTimer.all do delTimer pid t
  if (← getDev).clearWorkQueue.contains pid then drainHandshakeSendWq (some pid)

/-- peer_remove_after_dead (peer.c:94-150). -/
def peerRemoveAfterDead (pid : PeerId) : M Unit := do
  if ← branch .peerRemoveNotDead !(← getPeer pid).isDead then
    unsupported "peer_remove_after_dead: WARN_ON(!peer->is_dead)"
  keypairsClear pid
  timersStop pid
  -- flush_workqueue(packet_crypt_wq) twice (peer.c:116, 118): crypt work
  -- queued at a remove is W3b, outside the domain (the paths that queue it
  -- in this call do not reach a remove; across calls, requireNotPending)
  -- napi_disable, netif_napi_del
  -- flush_workqueue(handshake_send_wq) (peer.c:129): every queued item
  drainHandshakeSendWq none
  if (← getDev).numPeers == 0 then invariant "--num_peers below zero"
  modifyDev fun d => { d with numPeers := d.numPeers - 1 }
  peerPut (some pid)

/-- wg_peer_remove (peer.c:156-165). Work this call queued for the peer (an
    earlier entry of the same message) runs at the flushes, in its section;
    work pending from an earlier call is excluded where it is read. -/
def peerRemove (peer : Option PeerId) : M Unit := do
  if ← branch .peerRemoveNull peer.isNone then return
  let some pid := peer | invariant "unreachable"
  peerMakeDead pid
  -- synchronize_net(): no sleep on this kernel (Tiny RCU, PREEMPT_NONE)
  peerRemoveAfterDead pid

/-- wg_peer_remove_all (peer.c:167-184): every peer made dead, then each
    removed; the first peer's flushes drain whatever is queued for every
    peer. -/
def peerRemoveAll : M Unit := do
  free   -- wg_allowedips_free: avoid traversing each peer
  let dead := (← getDev).peerList
  for pid in dead do
    _ ← branch .peerRemoveAllIter1 true
    peerMakeDead pid   -- then list_add_tail(&peer->peer_list, &dead_peers)
  _ ← branch .peerRemoveAllIter1 false
  -- synchronize_net()
  for pid in dead do
    _ ← branch .peerRemoveAllIter2 true
    peerRemoveAfterDead pid
  _ ← branch .peerRemoveAllIter2 false

end Leanux.WG
