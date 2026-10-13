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

## Why two, not one

The 17.16 counterexample is a **produce-all-then-consume** account: op4's one
item leaves slot 0 occupied but uncleared (one consume, `consumer_head` 1,
`consumer_tail` 0, below `batch`), so op5 produces 1023 into slots 1..1023,
the 1024th wraps onto the still-occupied slot 0 and takes `-EPIPE` — exactly
one drop, 1023 in the ring.

The records refute produce-all-then-consume: the encrypt worker runs
**interleaved** with the producer (1024 consume sections and 14 reschedules
fall among op5's produces, not after them). With interleaving, the producer
wrapping past slot 0 also meets slots the consumer has advanced over but whose
batch of 16 has **not yet been zeroed** — the deferred-clear window of up to
`batch`-1 slots. For this trace and this recorded schedule the collision count
is two: op4's carried slot plus one slot inside the consumer's unflushed batch
at the instant the producer wraps. The count is therefore **a deterministic
function of (the prior batch's uncleared residue) + (the produce/consume
interleave) + (the batch-clear rule)**, not a constant; "two" is what this
schedule yields, and a different interleave would yield a different count.

## No new kernel instrument is needed

The producer's steps are deterministic in trace order (the mirror produces
in order). The only hidden fact is **when each encrypt-worker consume happens
relative to the produces**, and that is already carried by the existing remote
section records (kind-300 starts with the worker's unit word, 301 ends, 302
reschedules, 303 arms) that the scheduler loop replays. So the mirror can
reproduce both drops from records it already consumes; the tier adds no record
kind and no kernel patch. (The one sub-fact the implementer must still pin from
the existing coverage stream is the exact produce-vs-consume ordering within
op5's BH region — the PC order in `coverage.jsonl` settles it; it is an
implementation detail of the tier, not a missing instrument.)

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

## The mirror's current divergence

Per 17.16 the mirror's account of this trace yields **one** `-EPIPE`
(1023 in the ring), because its staged-send path does not interleave the
encrypt-worker consume at the recorded granularity. Confirming the live count
needs the trace inside a suite: the Linux-only probe
(`scripts/wg-w7-tier-probe.py`) runs it today, but `evaluator.check --trace`
rejects a trace that is in no suite (`ValueError: no trace '...' in the
selected suites`). The tier's first step is therefore to register a
`w7-tier` suite so the mirror replays the recorded schedule; the expected
pre-fix result at op 5 is a control-flow/`-EPIPE`-count mismatch, and the
post-fix result agreement.

## The tier

A `w7-tier` suite and `tier()` traces in the corpus script, outside the
default suites (the per-trace cost is large; each bulk child is a separate
chunk):

| Trace | Shape | Checks |
| --- | --- | --- |
| `w7_ring_wrap` | op4 one item, op5 1024 (exists) | the two-drop interleave; 1023 sent |
| `w7_ring_1023` | op5 1023 after the one-item op4 | the boundary that still fits (one carried slot, no extra drop): 1023 sent, zero dropped on the wrap |
| `w7_ring_1025` | op5 1025 | drops grow with the overflow; the count the interleave yields |
| `w7_ring_fresh_1024` | 1024 with **no** prior op4 item | the ring with no carried residue: tests whether the interleave alone drops any |
| `w7_ring_consumer_ahead` | op5 1024 with a `wait` that lets the encrypt worker drain before the producer wraps | the batch-clear catches up; fewer or zero drops |

Decisions and operands: `createDataEpipe` (`send.c:322`) fires per drop;
the `-EPIPE` operand is the ring-full test's occupancy, already an
`A3` comparison through `PtrRing.full`. Hidden inputs: none new; the dst
clock (kind-208), the workqueue arms (307/303) and the section schedule
(300/301/302) are the existing instruments. Harness budget: the dedup'd rows
are 3.3 MB for the two children at the wrap (P-A), inside the 16 MiB limit at
one bulk trace per chunk; `wait_ms` 1000 is the default; each new bulk trace
is its own chunk. The `consumer_ahead` and `1025` traces must be re-measured
with the probe for their row volume before they join (P-A is per-trace).

## Estimate

About 1.0 WU: the suite and four new traces (0.2), the probe re-measurement of
the two new bulk shapes (0.1), the control-flow interleave in the batch/scheduler
path with the existing ring primitives (0.5), and the claim point plus a one-off
mutant that drops one `-EPIPE` and must be rejected (0.2). No kernel rebuild
(no instrument change); the oracle stays s1.

## Leftovers

`.worktrees/w7-tier/.artifacts/w7-tier/wrap-s1-{1,2}` (the two probe runs and
their reports), `.artifacts/check/wrap-s1` (the aborted check), `.lake` (copied);
all ephemeral.
