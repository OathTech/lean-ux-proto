# Dispatch order: the unit a section runs is recorded (2026-10-11)

Decision [USER 2026-10-11]: option A: the order in which Linux dispatches
queued deferred units is recorded at the source, not assumed from queue order
and not taken as a placement the check reruns.

Stream: `task/dispatch-order` on the interface commit. Kernel change:
record-only (the approved class); the merge's signoff covers the new identity.

## 1. The gap

`s2_index_collision` configures two peers whose handshake initiations are both
queued by `wg_up` (`wg_packet_send_queued_handshake_initiation`, send.c:55-83,
once per peer in `peer_list` order). `handshake_send_wq` is `WQ_UNBOUND`
(device.c:338): its pool may run the two items in either order. The mirror ran
`sendWorkQueue` oldest first (`Env.runSendWorkers`). When Linux ran peer B's
item first, the records still matched one by one, since the index draw and the
ephemeral are consumed in record order, while the encrypted static was built
for the wrong remote static: a semantic mismatch at `wg_observe`, in about two
of three fresh-guest runs and in none of the chunked full checks (the pool's
state differs). Nothing in the records named the peer: the kind-300 section
start carried only the function's address.

The same assumption sat in the clear work (`runOneClearWorker`), the tx worker
(`runCryptWorkers`, per-peer `transmit_packet_work` on `packet_crypt_wq`) and
the timer pass (`fireTimer`: several peers' due timers of one kind were
"outside the domain (their order)").

## 2. The records (kernel/patches/gen-choice-stream.py)

Three generic, record-only changes at the interception points that exist:

| Record | Where | Payload | Before |
|---|---|---|---|
| kind 300, section start | `kcov_dispatch_start` (process_one_work, handle_softirqs, call_timer_fn) | `{func, unit}`, 16 bytes: the work item's address, the timer's, or 0 for a softirq | `{func}`, 8 bytes |
| kind 303, the arm record | `mod_timer` (`kcov_timer_arm`) | `{jiffies, expires, timer}`, 24 bytes | `{jiffies, expires}`, 16 bytes |
| kind 307, the queue record (new) | `__queue_work`, after `trace_workqueue_queue_work` (workqueue.c:2356), the one point every queued item passes once its pending bit is set | `{work, func}`, 16 bytes, at the caller's return address | none |

The queue record is written only for a work function in the armed dispatch
set, in a recording context (the trace's syscall, a section), gated by
`KCOV_DISPATCH_ARM_RECORDS` like the arm record; lock-free like
`kcov_timer_arm`. Work the kernel queues outside the set (linkwatch, RCU,
vmstat) records nothing, as before. A `__queue_work` from a timer's callback or
a NET_RX section lands in that section's stream; from the syscall, in the task
stream; the harness orders both by sequence number (`hidden_records`), so a
queue record always precedes the start of the section that runs its unit.

Addresses are opaque to the mirror. A unit's address is fixed for the life of
its owner (`peer->transmit_handshake_work`, `transmit_packet_work`,
`clear_peer_work`, the five `timer_list`s; the device's per-CPU crypt work and
`incoming_handshake_work`), so it names the unit across re-queues and re-arms.

## 3. The harness (evaluator/check.py)

- `pair_sections` requires the 16-byte start (a kernel without the identity is
  an `invalid_coverage` outcome, never a silent fallback); the function is
  word 0.
- Kind 307 resolves to class `queue` at the queued function's symbol
  (`('queue', '<symbol>:0')`), as a section resolves at its dispatched
  function's; an undeclared function is a problem, as for any record.
- `dispatch_problems`, per child in sequence order: a queue record or an arm
  record names a unit; a section start must name a unit queued or armed
  earlier and not dispatched since, and consumes it. Problems (the trace
  fails): a dispatched unit never queued or armed; a work item queued while
  already queued (since the claim-point robustness landing, a second
  instance, consumed by its own section); a non-softirq section without its unit. Units still queued
  or armed at the trace's end are counted in the report (`dispatch units left
  queued/armed`), not failed: an unfired timer is normal, and work that outlived
  the guest's wait is the mirror's existing refusal.
- `jiffies_problems` reads the 24-byte arm record's first two words as before.

## 4. The mirror (Leanux/Kernel/Defs.lean, Leanux/Env.lean, Leanux/WG/State.lean)

- A hidden site per work-item function, kind `queue`, ids 300 + the worker's
  index (`HiddenSite.queued`): the send, receive, encrypt, tx, decrypt and
  clear workers (timers arm, softirqs are not queued). The section-start sites
  are 16 bytes, `mod_timer_arm` 24.
- `queue_work`'s PENDING bit is modeled per unit, as the C has it
  (`queue_work_on`'s `test_and_set_bit(WORK_STRUCT_PENDING_BIT)`,
  kernel/workqueue.c): a per-peer unit (the send, tx and clear work) is
  pending while it is in its queue, which the mirror already tested before
  queueing; a device-level unit (the encrypt and decrypt workers' per-CPU
  work, `incoming_handshake_work`) is pending while its worker index is in
  `World.pendingWork` (`queueDeviceWork`). A queue attempt of a pending
  unit does nothing and consumes no record. One that queues consumes the
  queue record at that point (`recordQueued`, in `Send.lean`,
  `Receive.lean`, `Timers.lean`) and keeps the address with the unit
  (`World.unitPeers`); a re-queue at another address is a hidden mismatch.
  The unit's section start clears its pending bit (`hidden` of a section
  start: `process_one_work` clears it before calling the function), so a
  later queue attempt queues it again, with a new record, and a dispatched
  unit may find its data queue empty and run with nothing to do. The flood
  path discards the first flood packet's record with that packet's
  `net_rx` section, since it fills the handshake queue itself.
- At a dispatch, `peekUnit w` reads the unit from the start record without
  consuming it, and `resolveUnit w unit queue` names the queued peer by the
  address its queue record gave; an address no record gave, or a unit whose
  peer is not queued, is a hidden mismatch.
- An association lives as long as the C object that embeds the work struct
  or the timer (the simulation-target review, 2026-10-12, section 4.3): a
  peer's units (`transmit_handshake_work`, `transmit_packet_work`,
  `clear_peer_work`, the five timers) are retired at the peer's release
  (`kref_release`, `retirePeerUnits` in `peerPut`), the device's at
  `free_netdev` (`retireDeviceUnits` at the end of `wgDestruct`, with the
  pending bits). A later record at one of those addresses belongs to the
  new object the allocator put there, which starts its own association; a
  fresh device's peer ids restart. Before the rule, a peer re-added at its
  predecessor's address resolved to the released peer ("the dispatched
  unit is peer 0's, which is not queued"); `l_remove_readd_queued` and
  `l_delete_create_send` show the reuse (the same address in the records)
  and agree. The net namespace's `cleanup_net` unit outlives the device
  and is not retired (one namespace per trace).
- The first version captured the queue records out of band and paired them
  with the queued units at dispatch, by count. The full check on the
  dispatch-order oracle failed five transmit traces with "N queue records
  for 1 queued units": each `wg_xmit` queues the tx worker once (one record
  per operation, as the records show), and the tx worker dispatched at the
  encrypt worker's `cond_resched` (`Env/Batch.lean`) never consumed them,
  so they accumulated until a dispatch outside that path counted them.
  Consuming the record where the C queues removes the pairing by count.
- `runOneSendWorker`, `runOneClearWorker` and the tx loop of
  `runCryptWorkers` run the named unit and remove it from its queue; without
  an identity (the domain filter's placeholders; a record with a zero unit)
  they keep the head of the queue.
- `armTimer` keeps the arm record's timer address (`World.timerUnits`:
  address, peer, timer). `fireTimer` runs the timer the section names; it
  must be that callback's kind, pending and due, else a hidden mismatch.
  Several due timers of one kind are no longer outside the domain when the
  records name them; without an identity the one-due rule stands.
- Not changed: `Env/Batch.lean`'s `condResched` still takes the tx queue's
  head for a crypt worker it runs at a switch (W4+W7 B's file; it can adopt
  `peekUnit`/`resolveUnit` from `Defs.lean`); the receive, decrypt and encrypt
  workers are single units per device, so their queue records only pair.

## 5. Replays of earlier captures

Captures made before the identity word (evaluator/test_model_replay.py) are
widened with a zero unit (`widen`): a zero unit is "no identity", under which
the mirror keeps the legacy rule, so the contended-host regressions stay
replayable. Live runs cannot take that path: `pair_sections` refuses an
8-byte start, and `dispatch_problems` refuses a work section with unit 0.

## 6. Evidence plan (the coordinator, on the rebuilt kernel)

1. Rebuild the oracle (`LEANUX_KERNEL_PROFILE=net-choice`) and the control
   kernel (`net-choice-actl`); record both identities in the identity files.
2. `s2_index_collision` alone, 10 fresh guests: 10/10 agreement, with the
   dispatch order visible in the records; keep one B-first capture
   (`model-inputs.jsonl`) for the replay mutant.
3. The full check; the scoped mutants (Env.lean, Defs.lean, State.lean) and
   the D3 set; the controls.
4. Mutant Q-M1 (`scripts/wg-mutants.py`, pending the capture): the send
   worker runs the queue head, ignoring the named unit. Rejected
   deterministically by replaying the B-first capture, and live by
   `s2_index_collision` whenever Linux dispatches peer B first.

What the record pays for: the s2 defect above; W3+W12's several peers'
timers in one pass; the tx workers of several peers.

## The pending-handshake guard, retired (2026-10-14)

`requireNotPending` (State.lean) stopped any path that reads or changes
state the queued handshake send worker also touches, unless the work was
queued in the same system call: the worker's timing was unrecorded when the
guard was written. With the section records and the scheduler loop the
worker runs exactly where its section is, so the paths are determined. The
stop excluded ordinary simultaneous initiation on one CPU (the pre-release
review's finding 3): a peer's initiation arriving while wg0's own is queued.

Measured on s2 with `corpus/wireguard/p_sim_init_*` and the held traces
(`scripts/wg-w47-corpus.py --held`): a batch of one `wg_xmit` without a
session (queues the send worker, `handshake_send_wq`, unbound) and one
injected initiation (queues the receive worker). The remote stream at the
batch, by sequence number, ran the send worker first in some children and
the receive worker first in others:

- `p_sim_init_batch_recv_first`: in one run both children ran the send
  worker first (seq 17, the receive worker at seq 33; observe 148 twice,
  the trace agreed); in the next run the pc child ran the receive worker
  first (observe -EAGAIN) and the cmp child the send worker first (148).
- `p_sim_init_batch_send_first`: the pc child send first (seq 17, 32), the
  cmp child receive first (`wg_packet_handshake_receive_worker` seq 75,
  `wg_packet_handshake_send_worker` seq 91); observe 148 against -EAGAIN
  (the response roams the endpoint to the injector before the initiation
  goes out, so the listener sees nothing).
- `p_sim_init_two_peers`: both children receive first; the two send
  workers' order differed; observe 148 against -EAGAIN.

On every receive-first capture the old mirror stopped at peer.c:75
(`wg_peer_get_maybe_zero` in `consume_initiation`: "a reference count the
handshake worker also changes races the pending handshake worker"); with
the guard retired it replays each child's capture to that child's returns
([0, 0, 4, 148, 0] and [0, 0, 4, -11, 0] for the two-peer trace). The two
three batch traces are outside the harness's domain by its determinism
rule (`harness/linux.py`, the comparison child must rerun to identical
observations), not the mirror's: the review's finding 5. They are held
outside every suite with that reason (`--held`); the sequential trace is
in the `wireguard` suite.

The guard is a no-op; its callers and `World.queuedThisCall` are dead and
go in a later cleanup. A section the scheduler cannot place stays a hidden
mismatch.

