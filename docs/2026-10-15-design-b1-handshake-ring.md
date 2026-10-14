# B1: the handshake queue as the `PtrRing` the crypt queues use — design, 2026-10-15

Lane B1 of [the parallel plan](2026-10-14-wireguard-parallel-plan.md), from
audit items I1 ([the handshake audit](2026-10-13-audit-handshake.md)) and F10
([the receive audit](2026-10-13-audit-receive.md)). Written by a fork of the
coordinator [AGENT]; a Linux-only probe on the s4 oracle (section 8) settles
the one open fact. No implementation here.

## 1. Target

`wg->handshake_queue.ring` is a `ptr_ring` of `MAX_QUEUED_INCOMING_HANDSHAKES`
= 4096 slots (`device.c:358-359`, `messages.h:51`), batch 16. The mirror holds
it as `Device.handshakeQueue : List (List UInt8 × SkbSource)`
(`Leanux/WG/Types.lean:446`) with a length full-test (`Receive.lean:476`),
while the crypt rings were repaired to `PtrRing` after the simulation-target
review's 4.1 (commit 4b9dcaf, 2026-10-12). The review's counterexample applies
unchanged: a consumed slot stays occupied until a batch of 16 clears it, so
Linux's produce fails at 4096 minus the carried slots and the mirror's at 4096.

The change: the handshake ring becomes `PtrRing (List UInt8 × SkbSource)`,
produced and consumed by the same operations as the crypt rings
(`Leanux/WG/PtrRing.lean`), so that the ring's occupancy, cursors and
batch rule are the C's at every produce and consume, including the flood's.
The counter `handshake_queue_len` (`Device.handshakeQueueLen`) is untouched:
it is the C's atomic beside the ring, and lane B4 owns how the under-load
test reads it.

## 2. The kernel paths, verified (`.deps/linux` 6.12.110)

- **Init.** `wg_packet_queue_init(&wg->handshake_queue,
  wg_packet_handshake_receive_worker, MAX_QUEUED_INCOMING_HANDSHAKES)`
  (`device.c:358`; `queueing.c:24-40`): `ptr_ring_init` of 4096 entries,
  `__ptr_ring_set_size` (`ptr_ring.h:474-484`) with batch
  `SMP_CACHE_BYTES * 2 / sizeof(void *)` = 128 / 8 = 16, kept since 16 is
  not above size / 2; the three cursors at 0. `PtrRing.init 4096` computes
  the same batch (`Types.lean:211-215`).
- **Produce** (`receive.c:552-571`). `rng_is_initialized` (:552); then
  either arm produces through `__ptr_ring_produce` (`ptr_ring.h:104-116`):
  `-ENOSPC` when the producer's slot is occupied, else the pointer stored
  and the producer advanced with wrap. Above half the ring
  (`handshake_queue_len > 2048`, :554) the lock is a `spin_trylock_bh`
  (:555) with `ret = -EBUSY` when it fails; otherwise `ptr_ring_produce_bh`
  (:560, `ptr_ring.h:158-166`). A nonzero `ret` drops the skb (:561-565,
  `dev_kfree_skb` at :585) **without** touching the counter; success
  increments it (:567), draws the CPU (:568) and queues the work (:570).
- **Consume** (`receive.c:206-218`). `ptr_ring_consume_bh` (`ptr_ring.h:361-370`,
  `__ptr_ring_consume` :291-303): the peek (:169-174) and, on an item,
  `__ptr_ring_discard_one` (:247-289): the head advances; when
  `consumer_head - consumer_tail >= batch` or the head reaches the size, the
  slots from the old head down to the tail are nulled and the tail catches
  up; at the size both cursors return to 0. Then the packet, `dev_kfree_skb`,
  `atomic_dec` (:215), `cond_resched` (:216). `PtrRing.consume` and
  `PtrRing.discardOne` are these lines (`PtrRing.lean:47-70`, with the
  three `#guard`s).
- **Drain at `wg_stop`** (`device.c:130-132`): `ptr_ring_consume` until NULL,
  then the counter set to 0. On an empty ring the loop peeks NULL and
  changes nothing: the cursors and any carried slots **persist across
  down and up**. The ring is reinitialised only with the device
  (`wg_packet_queue_free(…, true)`, `device.c:258`, purge then `kvfree`).
- **Who takes the producer lock.** `handshake_queue.ring.producer_lock` is
  taken at `receive.c:555` and (inside `ptr_ring_produce_bh`) :560 only;
  `ptr_ring_consume(_bh)` and `ptr_ring_cleanup` take the consumer lock or
  none (verified by grep over `drivers/net/wireguard/`). `wg_packet_receive`
  runs in softirq context on this one CPU (`CONFIG_SMP` unset, `NR_CPUS` 1),
  where a softirq cannot nest, so the trylock at :555 always succeeds and
  the two arms produce identically. This is the fact behind section 4.3.

## 3. Hidden inputs

None new; no kernel change; no new record kind. The ring's state is a
function of the trace: the producer's and consumer's order on one CPU is
already fixed by the section records (`net_rx` per datagram, the receive
worker's section) and the dispatch record of the first packet's
`queue_work_on`. The probe (section 8) confirms the one scheduling fact the
flood summary already assumes: a flood's whole batch is produced before the
receive worker runs, at 4097 packets as at 521 (one worker section opened;
the worker's `cond_resched` yields, kind 302, do not split it).

## 4. The mirror

### 4.1 State (`Leanux/WG/Types.lean`)

- `handshakeQueue : PtrRing (List UInt8 × SkbSource) :=
  PtrRing.init MAX_QUEUED_INCOMING_HANDSHAKES`, in place of the list, with
  the docstring naming `device.c:358` and the batch. The constant moves from
  `Receive.lean:36` to `Types.lean` beside `MAX_QUEUED_PACKETS` (Types is
  imported first).
- `handshakeQueueLen` unchanged. The docstring's claim that the counter
  "exceeds the ring's occupancy by one while a packet is processed" stays
  true of the logical count (`PtrRing.count`); physical occupancy is now a
  separate, visible fact.

### 4.2 Functions (`Leanux/WG/Receive.lean`)

- `packetReceive` (:465-484): the full test becomes `d.handshakeQueue.full`
  (physical occupancy, `__ptr_ring_full`), the append becomes
  `d.handshakeQueue.produce (msg, src)`, the counter increment as today. The
  decision `.rxProduceFailed` keeps its site (:561) and spans.
- `receiveStep` (:343-356): `match d.handshakeQueue.consume with | (none, _)
  => …workerConsumed false | (some (msg, src), ring) => …workerConsumed true;
  handshakeQueue := ring; receiveHandshakePacket; handshakeQueueLen - 1`,
  the shape of the crypt workers (`RxData.lean`, `Data.lean`). The consumed
  slot stays occupied until the batch rule clears it, as the C's does.
- `handshakeReceiveWorker` unchanged (the loop bound stays
  `MAX_QUEUED_INCOMING_HANDSHAKES`).
- `Device.lean:94-97` (`wg_stop`): the `unsupported` on a nonempty ring
  becomes `!d.handshakeQueue.empty`; the drain then leaves the ring as it
  is (the C's empty-ring loop changes no cursor) and sets the counter to 0.
  Today's `handshakeQueue := []` would be a silent reinit. `Device.lean:271-276`
  (`wg_destruct`): the invariant test becomes `.empty`; the purge may reset
  the field or not, the device dies with it.

### 4.3 Decisions, operands and the trylock arm

Every decision stays: `.rxQueueBusy` (:554), `.rxProduceFailed` (:561),
`.workerConsumed` (:212), `.stopDrainIter` (:130). No operand changes: the
full test compares pointers, not values the mirror holds.

The `> 2048` arm (`.rxQueueBusy` true) is today `unsupported "spin_trylock_bh
on a busy handshake queue"` (`Receive.lean:473-474`). On one CPU the trylock
cannot fail (section 2, last item), so the arm is in the domain and the stop
is a fiction. Proposed: the arm becomes exact, with one new constant-false
decision `rxTrylockFailed` at :555 (true span (556, 557) through the
`__ptr_ring_produce` inline, false span empty: the failure arm has no line
of its own, `ret` keeps `-EBUSY`), stopping `unsupported "unreachable: a
second producer on one CPU"` on its false side, the pattern of
`.rxRngNotReady` three lines above (:552, "the guest waits for the RNG").
Both arms then reach the same produce and the same `.rxProduceFailed`.

What this buys is honesty, not evidence: the arm is reachable only inside a
flood, whose producer sections the check discards by rule
(`evaluator/check.py:1043-1059`), and a single `wg_inject` always finds the
ring drained. It costs one decision and a kcov span; it is tactical
(section 13).

### 4.4 Tests at the unit level

`PtrRing.lean`'s three `#guard`s cover the counterexample, the batch rule and
the wrap on a 1024 ring. Add one on `PtrRing.init 4096`: batch 16; 521
produced and consumed leave slots 512 to 520 occupied, `consumerTail` 512,
`count` 0; 4087 further produces succeed and the 4088th finds the ring
`full`. This is the carry twin of section 7 in miniature, and the number the
probe measured (section 8).

## 5. Environment rules (`Leanux/Env.lean`, `Leanux/Env/Batch.lean`)

- **`Env.flood` (:791-848), the producer side.** The batch is produced in the
  C's order through the ring: the leading valids, then `count` invalid
  templates, each `if ring.full then dropped else produce; counter + 1`. The
  number of successful produces is now the mirror's own fact, `produced`.
  The one-CPU `last_cpu` summary and the discarded producer sections are
  unchanged. The `control` valid (the merged-injection negative control) is
  still not modelled; its slot is not accounted for, which matters only at
  the ring's capacity and only on a trace built to fail.
- **The invalid tail.** The leading valids run through the real worker as
  today, consuming from the ring. The tail's summary then consumes
  `produced - leading` items from the ring (`PtrRing.consume` per item: the
  batch rule runs, the carried slots are the C's) beside the fold of the
  tail's records; the counter drains to 0 as today.
- **The contract strengthened, exactly.** `floodTailEffect`
  (`Leanux/Kernel/Defs.lean:2249-2289`) folds whatever clock records it
  finds up to the section's stop. With `produced` known, the tail's length
  is predicted: each tail packet reads exactly one clock (`under_load_now`
  while the counter is at or over 512, the decay clock below it with
  `last_under_load` set, none below it with the static clear). The contract
  takes the expected count and fails closed when the records are fewer or
  more: a ring with the wrong capacity or batch then shows as a hidden
  mismatch on the twin traces, in the record stream, with no operand check
  needed. Cheap, exact, one class of mistake.
- **`floodExact`** (`LEANUX_FLOOD_EXACT`, the unsummarised execution of the
  pre-release review's section 8): the same producer loop, every packet
  through the worker; nothing else changes.
- **`Env/Batch.lean`** :146 and :268 (`isEmpty` → `empty`), :223
  (`Activation.occupancy`: `.length` → `.count`), :311 (the record-less
  dispatch filter). `requireDrained` at `Env.lean:773` and the stop drain
  at :845: `.empty`.
- **No scheduling or timing assumption moves.** Everything the flood summary
  assumed about order it still assumes; the probe confirms it at the ring's
  size.

## 6. Harness and guest

No trace format change, no guest operation change, no kernel change. One
capacity finding from the probe (section 8): a flood past the ring needs
about 4100 fixture sends in one `io_uring_enter`, whose task-side
`KCOV_TRACE_CMP` stream (the sends' own comparisons, about 345 records per
packet, which the mirror does not model) exceeds the guest's comparison
area, `(CAPACITY - 1) / 4` = 1,048,575 records (`harness/guest.c:51,
2649-2650`). The coverage child completes the same traces well inside its
areas (2.32 M task and 1.42 M remote words of 4 M). The twin traces of
section 7 therefore need the **comparison area doubled** (8 M words, 64 MiB,
for the task comparison area; the PC areas and the remote area unchanged),
a guest-and-`harness/trace.py` constant, no change to the guest's memory
(`-m 256`, which sets epoll's `max_user_watches` and must not move). Whether
64 + 32 MiB of KCOV areas fit beside the guest's static tables in 256 MiB is
the build's first probe (section 12). Without it the twin traces are not
runnable and the capacity arms rest on section 4.4 alone.

## 7. Corpus

Two traces in `corpus/wireguard`, each in its own chunk as every under-load
trace is, both with the one leading valid of `e_underload_cookie`
(`e_underload_cookie`'s device, key and message):

| trace | ops | Linux (measured) | the list mirror | the ring mirror |
| --- | --- | --- | --- | --- |
| `e_ring_full` | `wg_flood` count 4096 + 1 leading (4097 sends) | 4096 produced, 1 dropped; the worker's first packet reads the counter at 4096 | 4097 queued: `.hsUnderLoad` operand 4097, the tail contract expects 4096 reads | 4096, 1 dropped: exact |
| `e_ring_carry` | `wg_flood` 520 + 1 (521), then `wg_flood` 4087 + 1 (4088) | second flood: 4087 produced, 1 dropped (slots 512 to 520 carried) | 4088 queued | 4087, 1 dropped: exact |

The first is the handshake twin of `w7_ring_fresh_1024`; the second of
`w7_ring_batch_clear` and `w7_ring_wrap` together (the batch rule and the
wrap in one flood). A third, `e_ring_over` (count 4200, 105 dropped), adds
nothing the first does not and is a probe trace only. The two traces reject
a list mirror in two independent ways once the contract of section 5 is in:
the operand at `receive.c:112` (`.hsUnderLoad`, the remote comparison
stream) and the tail's record count.

The sentinel set gains one mutant, run once and reported in the commit, then
kept only if it replaces a weaker sentinel: the batch rule at 1 instead of
16 on the handshake ring (`e_ring_carry` rejects it: 4096 produced instead
of 4087; `e_ring_full` does not).

## 8. The probe [AGENT, 2026-10-15, Linux only, s4]

Four traces, one boot, the cookie trace as the baseline, no mirror
(`.tmp/b1-probe/probe.py`, output under `.artifacts/b1-probe/run-1`, both
ephemeral). Read from the remote hidden stream (the worker's and the
softirq's records): kinds 300/301 are section start and stop, 208 the
8-byte clock reads at `receive.c:115` (under load, PC …ccbf) and :117 (the
decay, PC …cd80), 302 the worker's `cond_resched` yields.

| trace | sends | sections opened | clock reads (under load + decay) | packets consumed | dropped at produce | yields |
| --- | --- | --- | --- | --- | --- | --- |
| `e_underload_cookie` | 521 | 522 | 10 + 511 | 521 | 0 | 0 |
| `b1_ring_fresh_4097` | 4097 | 4098 | 3585 + 511 | 4096 | 1 | 9 |
| `b1_ring_carry_4088`, flood 1 | 521 | 522 | 10 + 511 | 521 | 0 | 0 |
| `b1_ring_carry_4088`, flood 2 | 4088 | 4089 | 3576 + 511 | 4087 | 1 | 8 |
| `b1_ring_over_4200` | 4201 | 4202 | 3585 + 511 | 4096 | 105 | 7 |

Sections opened = one `net_rx` per send plus one receive-worker section:
every send reached `wg_packet_receive` and the worker ran once per flood.
Packets consumed = the clock reads, one per packet. Each flood's figure is
the `ptr_ring` prediction exactly: a fresh ring takes 4096; after a drain of
521 (521 = 32 × 16 + 9) nine slots are carried and the ring takes 4087. The
batch is 16, the carry is physical, and the whole batch is produced before
the worker runs at this size too. Each big trace ran in about 3 s of guest
time. The comparison child failed each big flood with `empty_or_full_kcov`
at the flood op (section 6); the measurements above are the coverage
child's and the comparison child's remote records, which it wrote before
the failure. One cookie reply per flood was observed (`tx_packets` 1 and 2).

## 9. Out of scope (fail-noisy), and why

- `rng_is_initialized` false (:552): the guest waits for the RNG, as today.
- A second producer contending the trylock: impossible on one CPU; the
  false side of `rxTrylockFailed` stops `unsupported` (4.3).
- `wg_stop` with messages queued for a worker that has not run: `unsupported`
  as today (its timing), now tested on `.empty`.
- `wg_batch` cannot reach the ring's capacity (`BATCH_MAX` 1025,
  `harness/guest.c`): a batch of handshake injects stays well under 4082,
  so F10's "more than 4081 injects" route is the flood's, not the batch's.
- The merged-injection control's slot (section 5): a negative control only.

## 10. Proof-tree frames touched

The ring's type changes, so every frame that names `handshakeQueue` or the
worker's consume changes shape. On `main` (ca6b22e):

- `Leanux/Proofs/Logged/Operations.lean` :238-239 (`requireDrained`), :255-298
  (`floodLogged`: the producer loop and the tail's consume), the inject's
  drained test; `floodLogged_erases` (:301) and the three uses (:334, :365,
  :416).
- `Leanux/Proofs/Logged/Scheduler.lean` :87, :113 (`isEmpty` → `empty`).
- `Leanux/Proofs/Logged/Workers.lean` :107-111 (`handshakeReceiveWorkerLogged`
  and its erasure, through the step's consume).
- `Leanux/Proofs/WG/Keypairs/Evolution/Scheduler.lean` :61
  (`handshakeReceiveWorkerLogged_evolves`).
- Not touched: `ReplayWindow/Counterexamples.lean` (the decrypt ring only).

On `proofs/campaign` (campaign 1): the same four, plus nothing in
`Cookies/Gate.lean` and `Cookies/Load.lean` (they read the counter, which
stays) and nothing in `DeliveryOrder/Statements.lean` (generic over
`PtrRing`; its ring lemmas apply to the handshake ring unchanged, a small
gain). On `proofs/campaign-2`: as `main`. Both carry under the lag-and-repair
rule; the plan's cost note ("B1's is the next largest, since the handshake
ring's frames change type") stands, with the frames now listed.

## 11. Risks [AGENT]

- **The comparison area.** If 64 + 32 MiB of comparison areas do not fit in
  the 256 MiB guest, the twin traces have no runnable form at this memory
  and the capacity arms are unit-tested only. The guest's memory is not a
  knob here (epoll). Low probability: the areas are `vmalloc`ed and touched
  lazily, and the cookie trace's child already maps 64 MiB of areas.
- **Flood wall time at the claim point.** Each twin trace is a chunk of its
  own with about 4100 sends and a 0.7 MB record row; the probe's 3 s per
  trace says the suite's budget absorbs them.
- **The tail contract's count.** The strengthening of section 5 must match
  the C exactly at the threshold: a tail whose counter crosses 512 reads
  the under-load clock while `>= 512` and the decay clock below it, and no
  clock when `last_under_load` is clear. The boundary traces
  (`e_underload_511/512/513`) and the decayed trace are the regression set.
- **Carry across operations.** The ring's carried slots now persist across
  `wg_down`/`wg_up` and across every later operation, as the C's do. No
  corpus trace reaches the capacity after a drain except `e_ring_carry`, so
  no silent dependence on the old reinit is expected; the full check at the
  claim point is the test.

## 12. Estimate

In the plan's units (design 0.5 d, audit 0.5 d, build 2 d) and in WU (one WU
is WireGuard, about three weeks, [the scout](2026-10-12-kernel-scout.md)):

- the mirror, environment and logged frames (sections 4, 5, 10 on `main`):
  about 0.04 WU (a day), mechanical, the crypt-ring precedent was 177 lines
  over 9 files with the module already written;
- the comparison-area probe and change, the two traces, the one-off mutant
  (sections 6, 7): about 0.03 WU (half a day to a day);
- the claim point and controls: the usual hour at eight slots, plus the
  under-load chunks.

About 0.08 WU, or two days, as the plan has it. Order: the probe of section 6
first (it decides whether the traces exist), then the mirror change on
`main`'s tree, then the traces.

## 13. Decisions

For the user:

1. **The comparison area doubled for the twin traces** (section 6): a
   harness-and-guest constant, no kernel change, no guest memory change. The
   alternative is to leave the capacity arms at unit-level evidence (4.4)
   and keep the corpus at floods of 520. Recommended: the change, if its
   probe passes; the two traces are the only differential evidence of the
   handshake ring's occupancy, and they cost a constant.

Tactical [AGENT], stated for the record:

2. The `> 2048` arm becomes exact through `rxTrylockFailed` (4.3) rather
   than staying `unsupported`.
3. The flood tail contract predicts and checks its record count (section 5).
4. `wg_stop` leaves the ring's cursors as the C does; the field is not
   reinitialised below the device's own lifetime.
5. `MAX_QUEUED_INCOMING_HANDSHAKES` moves to `Types.lean`.

## 14. Artifacts

`.tmp/b1-probe/` (the probe script and its log) and `.artifacts/b1-probe/`
(the run: `boot.log`, `hidden.jsonl`, `probe.json`) in the design worktree:
ephemeral, deleted with the worktree. The command, for a rebuild:

```sh
LEANUX_SHARED_ROOT=/home/dev/projects/lean-ux-proto \
LEANUX_KERNEL_DIR=/home/dev/projects/lean-ux-proto/.artifacts/kernel-net-choice-s4 \
capped -- scripts/in-bundle python3 .tmp/b1-probe/probe.py --out .artifacts/b1-probe/run-1
```
