# W7 full-ring tier: the two silent drops at the 1024-item wrap

[AGENT, fork of the coordinator 2026-10-13] Reconnaissance for R4's drop
characterisation (the proof campaign, `docs/2026-10-13-charter-proof-campaign.md`)
and the W7 full-ring tier (`docs/2026-10-06-w4-w7-transmit-bulk.md` section 12).
Measured Linux-only on the s1 oracle (identity f098cf9e), two runs, identical.
No mirror or kernel edit; the mirror did not run (see "divergence").

## The question

The 1024-item `w7_ring_wrap` batch sends 1024 transport packets through a
`ptr_ring` of 1024 slots. Linux sends 1023 and drops **two** silently
(`tx_packets` 1025 = op4's 1 + op5's 1024; `tx_bytes` 65652 = 148 initiation
+ 32 staged keepalive + **1023** × 64 data; `tx_errors` 0, `tx_dropped` 0,
`wg_get` peer `tx_bytes` 65652). The ring counterexample of
`docs/2026-10-06-w4-w7-transmit-bulk.md` 17.16 predicts **one**. The two must
be explained exactly, not tolerated.

## The drop path (C, verified against `.deps/linux` 6.12.110)

A send-side silent drop has one path only, the ring-full `-EPIPE` arm:

- `wg_queue_enqueue_per_device_and_peer` (`queueing.h:157-179`) enqueues to the
  peer's `prev_queue` first, then `ptr_ring_produce_bh` into the encrypt ring;
  a full ring returns `-EPIPE` (`:174-176`).
- `wg_packet_create_data` (`send.c:316-333`) on `-EPIPE` calls
  `wg_queue_enqueue_per_peer_tx(first, PACKET_STATE_DEAD)` (`:322-323`) and
  returns without putting/freeing (the `likely(!ret || ret == -EPIPE)` early
  return at `:326`).
- `wg_packet_tx_worker` (`send.c:262-280`) peeks the dead packet, and because
  its state is `DEAD` not `CRYPTED`, frees it with `kfree_skb_list` (`:278`).
  No device counter is touched on this path; the drop is silent.

The ring itself (`include/linux/ptr_ring.h`): `__ptr_ring_produce` (`:104-116`)
fails (`-ENOSPC` → `-EPIPE` upstream) when `r->queue[r->producer]` is already
occupied. `__ptr_ring_discard_one` (`:247-289`) advances `consumer_head` on
each consume but **defers zeroing the consumed slots** until `batch` entries
have accrued since `consumer_tail` or the ring's end is reached
(`consumer_head - consumer_tail >= r->batch || consumer_head >= r->size`).
A WireGuard crypt ring has size 1024 and `batch` 16 (`__ptr_ring_set_size`,
`SMP_CACHE_BYTES*2/8`). So a consumed slot stays physically occupied, and
rejects a producer that wraps onto it, until its batch of 16 is cleared.

## The record evidence (op 5, both runs identical)

Task stream (the `io_uring_enter` producer): **1024** kind-208 dst-cache
clock reads, **2** kind-307 workqueue arms (the encrypt worker and the tx
worker, each armed once; later `queue_work_on` are no-ops while pending).

Remote stream (the kworkers): **1024** kind-300/301 sections, **1022**
kind-303 tx-worker arms, **1022** kind-208, 14 kind-302 reschedules, ~9
kind-110. The encrypt worker consumed and encrypted 1024 items but only
**1022** reached the tx-worker queue; the 2 missing are the drops, matching
the 1022 data messages op5 contributed to `tx_bytes`.

## Why two, not one [corrected at implementation, AGENT 2026-10-13]

The 17.16 counterexample is a **produce-all-then-consume** account: op4's one
item leaves slot 0 occupied but uncleared (one consume, `consumer_head` 1,
`consumer_tail` 0, below `batch`), so op5 produces 1023 into slots 1..1023,
the 1024th wraps onto the still-occupied slot 0 and takes `-EPIPE` — exactly
one drop, 1023 in the ring.

The reconnaissance above read the 1024 kind-300 sections as encrypt-worker
consumes interleaved with the produces. The sequence numbers refute that
reading: every record carries the kernel's global sequence number
(`kcov_choice_seq`, `kernel/patches/gen-choice-stream.py`), and at op 5 the
task stream's 1024 clock reads and 2 queue records are sequence 76 to 1101
while the first remote record is 1102. **Nothing of the kworkers ran between
two produces.** The 1024 sections are one `wg_packet_encrypt_worker` section
(with 5 of the 14 reschedules), one `wg_packet_tx_worker` section, and 1022
`net_rx_action` sections, the loopback delivery of each datagram the tx worker
sent, nested in its section (the three function addresses in the kind-300
payloads resolve so in `vmlinux`). The second queue record falls after the
1023rd clock read and before the 1024th: the `-EPIPE` arm's
`wg_queue_enqueue_per_peer_tx` queued the tx work at item 1023, and item 1024's
queue was the no-op of a pending work. Items 1023 **and** 1024 failed.

The account produce-all-then-consume is right; what it missed is the slot the
**session's keepalive** took. The response to the initiation (op 3) completes
the session and sends the staged keepalive through the same ring
(`wg_packet_send_keepalive` → `wg_packet_send_staged_packets` →
`wg_packet_create_data`): slot 0, consumed by the encrypt worker, uncleared
(`consumer_head` 1, `consumer_tail` 0). Op 4's item takes slot 1, consumed,
uncleared (head 2, tail 0, two below `batch`). Op 5's items 1..1022 take slots
2..1023; item 1023 wraps onto slot 0, occupied, `-EPIPE`; and because a failed
`__ptr_ring_produce` leaves `r->producer` where it is (:104-116), item 1024
meets the same slot and fails too. **Drops = items − (1024 − the uncleared
slots carried into the batch)**, a function of the ring's state at the batch,
not of any interleave; for this trace, 1024 − 1022 = 2.

## No new kernel instrument is needed

The producer's steps are deterministic in trace order, the kworkers run after
`io_uring_enter` returns, and the carried slots are the ring's own state, which
the mirror holds exactly (`Leanux/WG/PtrRing.lean`). The tier adds no record
kind and no kernel patch; the oracle stays s1.

## What the mirror must represent

The ring data structure is already exact: `Leanux/WG/PtrRing.lean`
(`full` on physical occupancy, `produce`, `discardOne` with the batch and
ring-end clear, three `#guard`s including the wrap) and `Leanux/WG/Types.lean`
`PtrRing`. The gap is **control flow, not data**: the batch/scheduler path
(`Leanux/Env/Batch.lean`, `Leanux/WG/Send.lean`'s staged-send enqueue) must
run the encrypt-worker `consume` interleaved with the producer's `produce`
at the granularity the section records dictate, so the ring's occupancy at
each produce matches Linux and the `-EPIPE` decision
(`Decision.createDataEpipe`, already declared at `Decision.lean:1284`, site
`send.c:322-323`) fires the correct number of times. No new decision, no new
ring semantics.

## The mirror's divergence: none [measured at implementation, AGENT 2026-10-13]

The reconnaissance expected the mirror to yield one `-EPIPE`; it had not run
the mirror. With the trace registered in a suite (`w7-tier`,
`evaluator/check.py`), the mirror as landed on main (the ring of
`Leanux/WG/PtrRing.lean`, the staged-send path, the scheduler loop)
reproduces both drops without any change: the keepalive's and op 4's slots
are carried exactly as the C carries them, `enqueuePerDeviceAndPeer` leaves
the producer in place on `-EPIPE`, and the kworkers run after the batch as
the records order them. Two things stood between the trace and the check,
both budgets: the mirror's branch report of the 1024-item batch is 126,531
labels against `MAX_BRANCHES` 32768 (`evaluator/protocol.py`, now 2^18), and
the session's 5 s persistent keepalive fired during the comparison child's
console drain after the batch (2.4 MB at about 0.5 MB/s), opening four
sections after the readout (the timer, the encrypt and tx workers, NET_RX:
"dispatch sections opened but not recorded", 1038 against 1034, in the
reconnaissance probe's own `sections.jsonl` too); the tier's sessions use
the 25 s keepalive.

## The tier

The `w7-tier` suite (`evaluator/check.py`, `TIER_SUITES`, run on request and
outside the default list; each trace is a bulk chunk by itself) and
`tier()` in `scripts/wg-w47-corpus.py`, five traces on the s1 oracle (six with the receive twin below), each
with the ring-full and `-EPIPE` outcomes in its expectations. Drops = items
− (1024 − the uncleared slots carried into the batch):

| Trace | Shape | Carried | Linux and the mirror |
| --- | --- | --- | --- |
| `w7_ring_wrap` | op4 one item, op5 1024 | 2 (the keepalive's slot 0, op4's slot 1) | 1022 sent; items 1023 and 1024 `-EPIPE` at slot 0 |
| `w7_ring_1023` | op4 one item, op5 1023 | 2 | 1022 sent; item 1023 `-EPIPE` |
| `w7_ring_1025` | op4 one item, op5 1025 | 2 | 1022 sent; items 1023 and 1024 `-EPIPE`; item 1025 `-ENOSPC` from `wg_prev_queue_enqueue` (the peer's `tx_queue` at `MAX_QUEUED_PACKETS`, 1024, holding the 1022 crypted and 2 dead items), freed by `wg_packet_create_data`'s error path |
| `w7_ring_fresh_1024` | no op4, op5 1024 | 1 (the keepalive's) | 1023 sent; item 1024 `-EPIPE` |
| `w7_ring_batch_clear` | op4 15 items, op5 1024 | 0 (16 consumed: the batch rule clears slots 0..15 at the 16th) | all 1024 sent |

All five agree (`.artifacts/check/tier-*-1`, 12,317 to 12,497 operand pairs
each). Decisions: `createDataEpipe` (`send.c:322`) per `-EPIPE`,
`enqueueRingFull` (`queueing.h:174`) per produce, `enqueuePeerQueueFull`
(`queueing.h:167`) at the 1025th. Hidden inputs: none new; the dst clock
(kind-208), the queue records (307), the arms (303) and the section schedule
(300/301/302) are the existing instruments. Harness budget: at one bulk
trace per chunk every trace stays inside the 16 MiB output limit;
`wait_ms` 1000 for the big batch, 200 for the first. The `consumer_ahead`
shape the reconnaissance proposed is replaced by `batch_clear`: a wait inside
one `wg_batch` cannot let the consumer ahead (the kworkers run after
`io_uring_enter`), but a first batch that completes a batch of 16 consumes
does, and yields zero drops.

### The receive twin [registered 2026-10-13, robustness]

The receive correspondence audit's F1 (`docs/2026-10-13-audit-receive.md`)
found `wg_packet_consume_data`'s `-ENOSPC` arm (receive.c:534-539, the
peer's `rx_queue` at `MAX_QUEUED_PACKETS`) ending in an `invariant` stop;
the mirror has the C's puts and silent free. Its trace, `w7_ring_rx_1025`
(`rx_1025()` in `scripts/wg-w47-corpus.py`: 1025 keepalive-sized data
messages in one batch, since the guest's `MAX_PAYLOAD` of 65536 bytes cannot
carry 1025 inner datagrams), is the tier's sixth trace. The 1024 inline NAPI
polls that follow meet the (c') placement ambiguity 1019 times; the
protocol's ceiling on open placements (`evaluator/protocol.py`,
`injected_messages`) is the trace's injected-message count, since one (c')
placement arises per `wg_queue_enqueue_per_peer_rx`, that is per data
message the fixture delivered, and a count above it is an invalid output;
the bound of 64 it replaces was a guess. The check's placement selection
(`section_agreement`) is two runs and a replay whatever the count, so the
selection runs over all of them. [AGENT 2026-10-15] Not quite: the mirror's
parser kept its own bound of 8 on the `napi_irq_before_put` vector, which
no run had reached because the twin's all-after run agreed outright on a
quiet box; on a loaded box the kernel takes the (c') placement at a few
polls and the before-put run was refused ("more than 8 entries"), failing
the twin at two claim points. The mirror's ceiling is now the records'
NET_RX section-start count, and the selection's cost is per section
(the W4+W7 design's section 17.10, "The ceiling, as the load corrected it"). `wg_packet_consume_data.enqueued` and
`enqueued_epipe` are `repeatable` (both outcomes in one operation: 1024
successes and the refusal). On s2 the trace agrees (15,404 operand pairs;
`invalid_output` before the ceiling, `opposite outcome covered` at
receive.c:531 before the repeatable marks).

### The claim point's failure, and a timer that is not one [AGENT 2026-10-13]

The audit wave's integration record (main f45bde8) named the gap "a timer
section inside a batch is not yet placeable by the scheduler"; the gap was
the crypt-ahead schedule below, and that wording is superseded.

The audit wave's claim point failed `w7_ring_fresh_1024` in this group
under seven guests with `expected section_stop:wg_packet_tx_worker (site
47), the record is site 100`, read at the time as a timer firing inside the
batch. Site 100 is the arm record: the kernel dispatched the tx worker at
an encrypt yield and it sent more items than the mirror's encrypt
activation had crypted; the rule is 17.18 of the W7 design (`cryptAhead`).
Shorter keepalives (1, 2 and 5 s) were tried to put a timer inside the
batch and cannot: the persistent keepalive is re-armed at every
authenticated packet, so it fires only after the last send, in the console
drain between operations, where no window records it; the 2 s and 5 s
variants fail the guest's opened-sections guard (`opened 1036, recorded
1032`) and the 1 s one as a bare observation difference (`tx_packets` 1026
against 1025, the keepalive sent between the batch's readout and the
observe, with no section in either window and the guard silent). A timer
whose effects fall between windows is outside the domain by construction;
the 1 s case shows the guard does not cover every such gap, a harness
matter noted, not changed.

## Estimate and the actual cost

The reconnaissance estimated about 1.0 WU, half of it a control-flow
interleave in the scheduler. There was no interleave to build: the mirror
change is nil, and the tier cost the suite registration, the five traces,
one evaluator bound, the sessions' keepalive, the design's correction and
the one-off mutant, about 0.2 WU, with no kernel rebuild; the oracle stays
s1. What the reconnaissance got wrong was reading the kind-300 count as
interleaved consumes without ordering the two streams by their sequence
numbers; the sequence number is the instrument that settles such questions
and should be the first thing read.

## Leftovers

The implementation worktree's `.artifacts/check/tier-*` (the five runs, the
two wrap attempts before the budgets, the regression run) and `.lake`
(copied); the reconnaissance worktree's probe runs; all ephemeral.
