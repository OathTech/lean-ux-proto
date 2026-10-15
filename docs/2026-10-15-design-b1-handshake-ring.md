# B1: the handshake queue as the `PtrRing` the crypt queues use — design v2, 2026-10-15

Lane B1 of [the parallel plan](2026-10-14-wireguard-parallel-plan.md), from
audit items I1 ([the handshake audit](2026-10-13-audit-handshake.md)) and F10
([the receive audit](2026-10-13-audit-receive.md)). Written by a fork of the
coordinator [AGENT]. Version 2 answers [the independent review](2026-10-15-design-b1-review.md)
(b826285, 13 findings, "build with the named changes"): section 15 takes
the findings one by one, and sections 2 to 13 carry the corrections. Three
Linux-only probes on the s4 oracle (section 8) settle the evidence plan:
the twin traces exist at the named sizes. No implementation here.

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
  `SMP_CACHE_BYTES * 2 / sizeof(void *)` = 128 / 8 = 16
  (`CONFIG_X86_L1_CACHE_SHIFT=6`), kept since 16 is not above size / 2; the
  three cursors at 0. `PtrRing.init 4096` computes the same batch
  (`Types.lean:211-215`).
- **Produce** (`receive.c:552-571`). `rng_is_initialized` (:552); then
  either arm produces through `__ptr_ring_produce` (`ptr_ring.h:104-116`):
  `-ENOSPC` when the producer's slot is occupied, else the pointer stored
  and the producer advanced with wrap. Above half the ring
  (`handshake_queue_len > 2048`, :554) the lock is a `spin_trylock_bh`
  (:555) with `ret = -EBUSY` when it fails; otherwise `ptr_ring_produce_bh`
  (:560, `ptr_ring.h:158-166`). A nonzero `ret` drops the skb (:561-565,
  `dev_kfree_skb` at :585) **without** touching the counter; success
  increments it (:567), draws the CPU (:568) and queues the work (:570).
- **The trylock is a compile-time constant on this build.** With
  `CONFIG_SMP` and `CONFIG_DEBUG_SPINLOCK` both unset
  (`kernel/config-x86_64-net-choice:258, 2058`), `spinlock.h:311-315`
  selects `spinlock_api_up.h`, whose `_raw_spin_trylock_bh(lock)` is
  `({ __LOCK_BH(lock); 1; })` (:75); `spin_trylock_bh` (`spinlock.h:409-411`)
  returns it. The arm at :555 cannot fail, whatever the context, and both
  arms produce identically. This is a build fact (section 4.3), not a
  scheduling argument.
- **Consume** (`receive.c:206-218`). `ptr_ring_consume_bh` (`ptr_ring.h:361-370`,
  `__ptr_ring_consume` :291-303): the peek (:169-174) and, on an item,
  `__ptr_ring_discard_one` (:247-289): the head advances; when
  `consumer_head - consumer_tail >= batch` or the head reaches the size, the
  slots from the old head down to the tail are nulled and the tail catches
  up; at the size both cursors return to 0. Then the packet, `dev_kfree_skb`,
  `atomic_dec` (:215), `cond_resched` (:216). The loop has no bound: it
  ends at the first NULL poll. `PtrRing.consume` and `PtrRing.discardOne`
  are these lines (`PtrRing.lean:47-70`, with the three `#guard`s).
- **Drain at `wg_stop`** (`device.c:130-132`): `ptr_ring_consume` until NULL,
  then the counter set to 0. On an empty ring the loop peeks NULL and
  changes nothing: the cursors and any carried slots **persist across
  down and up**. The ring is reinitialised only with the device
  (`wg_packet_queue_free(…, true)`, `device.c:258`, purge then `kvfree`).
  Measured (section 8): a `wg_down`/`wg_up` between two floods leaves the
  nine carried slots in place.

## 3. Hidden inputs

None new; no kernel change; no new record kind. The ring's state is a
function of the trace: the producer's and consumer's order on one CPU is
already fixed by the section records (`net_rx` per datagram, the receive
worker's section) and the dispatch record of the first packet's
`queue_work_on`. The probes confirm the one scheduling fact the flood
summary already assumes: a flood's whole batch is produced before the
receive worker runs, at 4097 packets as at 521 (one worker section per
flood, opened after every NET_RX section; the worker's `cond_resched`
yields, kind 302, do not split it).

## 4. The mirror

### 4.1 State (`Leanux/WG/Types.lean`)

- `handshakeQueue : PtrRing (List UInt8 × SkbSource) :=
  PtrRing.init MAX_QUEUED_INCOMING_HANDSHAKES`, in place of the list, with
  the docstring naming `device.c:358` and the batch. The constant moves from
  `Receive.lean:36` to `Types.lean` beside `MAX_QUEUED_PACKETS` (Types is
  imported first), **keeping its name in `Leanux.WG`**: campaign 1's
  `Cookies/Gate.lean:18-43` and `Cookies/Load.lean:10-32` unfold it by name.
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
- **The loop's fuel** (:359-361): `MAX_QUEUED_INCOMING_HANDSHAKES + 1`, not
  `MAX_QUEUED_INCOMING_HANDSHAKES`. `workerLoop` (`Defs.lean:1789-1793`)
  runs at most `bound` iterations and stops with `invariant drained`; a run
  that drains a full ring needs 4096 consuming iterations and the empty
  poll, 4097. With the bound at 4096 the mirror stops with "the handshake
  queue did not drain" on a full ring where the C ends normally (reachable
  on `floodExact` over `e_ring_full`, and on any later path that runs the
  real worker over a full ring; the crypt workers already use
  `MAX_QUEUED_PACKETS + 1`). The copies that carry the same bound and
  change with it: `Env/Batch.lean` (`Activation.run`'s bound for
  `.receiveWorker`), `Leanux/Proofs/Logged/Workers.lean:107-109` on `main`
  and both campaign branches, campaign 1's `Lifetimes/ReceiveWorker.lean:47-49`
  and `Lifetimes/BatchAudit.lean:186-188`, and the docstring of
  `LifetimeSafety/Statements.lean:1407-1409` ("the 4096-step exhaustion
  Stop" becomes a 4097-step one), a statement file under the proof gate.
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
on a busy handshake queue"` (`Receive.lean:473-474`). The trylock is the
constant 1 on this build (section 2), so the arm is in the domain and the
message is wrong about why it stops. Two options:

- **A. Exact, with a decision.** A new constant-false decision
  `rxTrylockFailed` at :555, declared by `Decision.lean`'s convention
  (`d label file line whenTrue whenFalse`, :588; `rxRngNotReady` at :1146 is
  the model): `whenTrue = []` (the failure arm has no line of its own:
  `ret` keeps `-EBUSY` and :561 takes it), `whenFalse = [(556, 557)]`, the
  `unsupported "unreachable: the trylock is the constant 1 on this build
  (spinlock_api_up.h:75)"` on the **true** side. Since the compiler folds
  the constant, the false span's witnesses coincide with `.rxQueueBusy`'s
  true span (555-558); harmless. Cost: the decision, its `kcov.json` span,
  `WGMore.lean:460-465`'s `packetReceive_ordinary` on `main` and both
  campaigns, campaign 1's copy `Lifetimes/ReceiveIngress.lean:50-60`. The
  decision is never exercised: `packetReceive` never sees the counter above
  2048 (an inject finds the ring drained; the flood produces through
  `Env.flood`'s own loop, section 5).
- **B. Keep the stop, correct its reason.** `.rxQueueBusy` true stops
  `unsupported "unreached: the counter exceeds 2048 only inside a flood,
  whose producers Env.flood summarizes; the trylock is the constant 1 on
  this build (spinlock_api_up.h:75)"`. No new decision, no frame touched,
  no arm hidden: the stop is fail-noisy and its reason is a build fact.

**Recommendation: B** [AGENT]. A decision no trace or unit test can reach
buys no evidence and costs four frames; the governing principle (a choice
point per C choice point, out-of-scope arms explicit and noisy) is met by
`.rxQueueBusy` with a true reason. If `Env.flood` is ever made to produce
through `packetReceive` itself, option A is the day's work then.

### 4.4 Tests at the unit level

`PtrRing.lean`'s three `#guard`s cover the counterexample, the batch rule and
the wrap on a 1024 ring. Add one on `PtrRing.init 4096`: batch 16; 25
produced and consumed leave slots 16 to 24 occupied (25 = 16 + 9),
`consumerTail` 16, `count` 0; 4087 further produces succeed and the 4088th
finds the ring `full`. At batch 32 the same 25 would leave 25 slots carried
and 4071 produces: the guard discriminates the batch, as the carry twin of
section 7 does, and the number is the one both probes measured (section 8).

## 5. Environment rules (`Leanux/Env.lean`, `Leanux/Env/Batch.lean`)

**`Env.flood` (:791-848), reworked exactly.** The C produces every packet
of the batch before the worker runs, and the full test depends on that
order, so:

1. **Produce the whole batch, in the C's order**, through the ring: the
   leading valids, then `count` invalid templates, each `if ring.full then
   dropped else produce; counter + 1`. A leading valid that finds the ring
   full fails closed (`invariant`: no corpus trace is built to lose one).
   `produced` (the successful produces) and `leading` (the valids produced)
   are now the mirror's own facts. The one-CPU `last_cpu` summary and the
   discarded producer sections are unchanged. The `control` valid (the
   merged-injection negative control) is still not modelled; its slot is
   not accounted for, which matters only at the ring's capacity and only
   on a trace built to fail.
2. **Run the real worker for the leading valids only**: `workerIter
   .receiveWorker none WG.receiveStep (do nestedResched .receiveWorker; pure
   false)` (`Defs.lean:1781-1784`) exactly `leading` times, each required
   to return other than `.ended` (`invariant` otherwise). Each step consumes
   its packet from the ring through `receiveStep` and reports its records
   and decisions as today. Not `handshakeReceiveWorker`: the whole loop
   would consume the tail through `receiveHandshakePacket`, which is the
   `floodExact` execution, not the summary.
3. **The tail summary** consumes `produced - leading` items from the ring
   (`PtrRing.consume` per item: the batch rule runs, the carried slots are
   the C's) and runs the per-packet contract below over the same count.
   The counter drains to 0 as today.
4. **The final empty poll**: one `WG.receiveStep` on the drained ring,
   required to return `false` (`invariant` otherwise), so the C's last poll
   (`.workerConsumed false`, `receive.c:212`) comes after the tail, where
   the C has it, and not after the leading valids as today.

The Logged copy (`floodLogged`) and its erasure theorem follow the same
four steps (section 10).

**The tail contract, per packet.** `floodTailEffect`
(`Leanux/Kernel/Defs.lean:2249-2289`) folds whatever clock records it finds
up to the section's stop. With `produced` known it becomes a simulation of
the tail, packet by packet, over the counter and the running
`last_under_load`: tail packet `i` (0-based) reads the counter at
`receive.c:112` as `produced - leading - i` (the leading valids have each
decremented it; each tail packet decrements after its own processing).
For each packet, in order:

- counter at or above 512: the next record must be an `under_load_now`
  read (`.underLoadNow`, :115); `last := some now`;
- below 512 with `last = some saved`: the next record must be the decay
  read (`.birthdateExpired`, :117); if `saved + 1 s ≤ now` then
  `last := none` (:118-119);
- below 512 with `last = none`: no record for this packet (:116 false,
  nothing read).

Between packets only `resched` records (the worker's yields) and the cut
sites are dropped; after the last packet, after any trailing yields, the
next record must be the section's `stop`. Any other site, a record where
none is predicted, or a predicted record missing, is a hidden mismatch,
fail-closed. An expiry inside the tail (a slow host: the decay phase took
4 ms of coarse clock in the probes, against the 1 s expiry) is the C's
own outcome and is followed, never a failure. On the baseline this
predicts 10 under-load reads (the leading valid at 521 and the tail at
520 down to 512) and 511 decay reads, which is what both children
recorded; on `e_ring_full` 3585 and 511; on `e_ring_carry`'s second flood
3576 and 511 (section 8). A ring with the wrong capacity or batch shows
as a wrong count in the record stream, with no operand check needed.
Cheap, exact, one class of mistake.

**`floodExact`** (`LEANUX_FLOOD_EXACT`, the unsummarised execution of the
pre-release review's section 8): step 1, then `handshakeReceiveWorker`
over the whole ring with the corrected fuel (4.2); nothing else changes.

**`Env/Batch.lean`** :146 and :268 (`isEmpty` → `empty`), :223
(`Activation.occupancy`: `.length` → `.count`), :311 (the record-less
dispatch filter), and `Activation.run`'s bound (4.2). `requireDrained` at
`Env.lean:772-773`: `.empty`.

**No scheduling or timing assumption moves.** Everything the flood summary
assumed about order it still assumes; the probes confirm it at the ring's
size.

## 6. Harness and guest

No trace format change, no guest operation change, no kernel change, no
identity change. A flood past the ring needs about 4100 fixture sends in
one `io_uring_enter`, and the two probes found, in turn, the two guest
limits that stand between such a flood and the comparison child:

- **The task comparison area.** The sends' own `KCOV_TRACE_CMP` records
  (about 345 per packet, unmodelled fixture work) reach about 1.41 M for
  4097 sends, past `(CAPACITY - 1) / 4` = 1,048,575 records
  (`harness/guest.c:51, 2649-2650`). Probe 1 failed there
  (`empty_or_full_kcov`).
- **The block table.** `split_hidden` in comparison mode writes
  `cmp_block[kept]` for every kept record of the area it is given
  (`guest.c:1079`), and it is given the task area too (:2680) although the
  blocks are only read for the remote area (`print_records` with
  `cmp_block`, :2687); `cmp_block` has `CAPACITY / 4` entries (:464). With
  the area doubled, probe 2's comparison child ran the whole flood (4099
  sections opened, none dropped) and was then killed by the overflow
  before printing the operation's rows: the remote wrapper exits 1 for a
  signalled trace process (:1489), which the parent reports as status 256.
- **The host's merged bound.** With the table sized too (probe 3), both
  children completed both traces, and the host rejected the run:
  `harness/linux.py:585` merges the task and remote comparison rows of an
  operation into one, and :726-727 bounds the merged count by
  `2 * ((KCOV_CAPACITY - 1) // 4)` = 2,097,150, the sum of two streams at
  the old limit; `e_ring_full`'s flood has 1,411,041 + 764,762 = 2,175,803.
  The bound becomes the sum of the two streams' new limits, 3,145,725.

**The change** is therefore wider than a constant. One `CAPACITY` sizes
the task area (:1935, :1939), the remote area (:1447-1451, and
`remote_size`, which also sizes the kernel's per-section area for
task-context sections, `kernel/kcov.c:903-915`), the child area
(:2065-2066), the tables `cmp_block` (:464), `distinct` (:503) and
`ranges` (:505), and both full checks (:2649, :2675); on the host one
`KCOV_CAPACITY` (`harness/trace.py:172`) bounds every stream
(`harness/linux.py:717, 726`; `evaluator/protocol.py:325`) and is pinned
by `harness/test_trace.py:520-524` and `evaluator/test_evaluation.py:147`.
Doubling the task comparison area alone takes: a second guest constant
for that area and its full check; `cmp_block` sized by it, or not written
for the task area at all (the cleaner fix: the blocks are a remote-area
notion); the host's merged comparison bound raised to the sum of the two
streams' limits, with the per-stream full checks kept in the guest for
every area (they are instrument guards on the trust surface, and the
merged bound alone would not catch one stream overflowing into the other's
headroom); the two tests extended. About 40 lines across the guest,
`trace.py`, `linux.py`, `protocol.py` and the tests. Probe 3 ran with the
guest side of exactly this change (the constant, the area, its check, the
table) and the host side untouched, which is why the host rejected it.

**The larger area is per trace, not for every trace** (the build's
regression, section 16): the comparison child's task area is
`TASK_CMP_CAPACITY` only for a trace with a flood of more than
`FLOOD_BIG_AREA_SENDS` = 2048 sends (count, leading valids and control;
`guest.c` `task_capacity`, `harness/trace.py` `task_cmp_capacity`, the
host's merged bound per trace, pinned by `test_trace`). The mapping is
shared with every process the trace forks, and `fork` copies its page
tables (`copy_pte_range`, `vm_normal_page`, `mm/memory.c:1139-1189, 597`),
work the comparison child records as about four distinct comparisons per
page; the seccomp probes fork a child per operation, and at twice the
pages their rows grew by 1.7 MB each, past the 16 MiB captured-output
limit on single-trace chunks. With the area sized per trace the seccomp
traces' output is the former size to within a boot's variation.

**Memory, measured.** `KCOV_INIT_TRACE` allocates with `vmalloc_user`
(`kcov.c:718`), which is `__GFP_ZERO` (`mm/vmalloc.c:4063-4069`): the pages
are committed and zeroed at once, not touched lazily. The comparison
child of a flood holds the task area, the remote area and the 32 MiB area
the worker's remote section allocates (`kcov_remote_area_get`, cached by
`kcov_remote_area_put`): 96 MiB today, 128 MiB with the doubled task area,
beside the guest's touched tables (`dedup_table` 16 MiB, fully touched by
a 1.4 M-record pass; `distinct` and `bulk_out` 16 MiB each, partly;
`cmp_block` 2 MiB) in the 256 MiB guest (`MemTotal` 241,748 kB once the kernel has
its own). Measured in probe 3 from `/proc/meminfo`, outside every window:
in the comparison child `VmallocUsed` goes from 67,728 kB before the task
area (the remote area and the worker's section area, which the kernel
caches across children) to 133,392 kB at the end of the flood, the 128 MiB
of areas plus 2 MiB; `MemFree` ends at 76,816 kB and `MemAvailable` at
73,136 kB. The coverage child ends at 100,560 kB of vmalloc and 120,744 kB
free. The areas fit with about 75 MiB to spare. The guest's
memory (`-m 256`, `harness/linux.py:867`) does not move: it sets
`max_user_watches` (`EXPECTED_MAX_USER_WATCHES`, `linux.py:146-157`) and
the rate limiter's table (`ratelimiter.c:173-177`), both from total
memory; `EXPECTED_MAX_USER_WATCHES` is re-checked after the guest rebuild
all the same, since a changed initramfs can move it.

**Remote comparison area, measured.** The comparison child's flood has
764,762 remote comparison records at 4097 sends (`e_ring_full`) and
763,008 at 4088 (`e_ring_carry`'s second flood), of the 1,048,575-record
limit: a margin of 1.37, so the remote area stays at its size. The task
comparison stream is 1,411,041 and 1,407,912 of the doubled limit
2,097,151, a margin of 1.49. The projection from the cookie trace (783 K)
was 2 percent high.

## 7. Corpus

Two traces in `corpus/wireguard`, each in its own chunk as every under-load
trace is, both ending at their last flood (the time bound of section 11
counts to the end of the last operation, before its rows are printed; a
trailing `wg_observe`/`wg_get` would add its 0.4 s wait and the flood's
printing to the count), both with the one leading valid of
`e_underload_cookie` (its device, key and message):

| trace | ops | Linux (measured, section 8) | the list mirror | the ring mirror |
| --- | --- | --- | --- | --- |
| `e_ring_full` | `wg_create`, `wg_set`, `wg_up`, `wg_flood` count 4096 + 1 leading (4097 sends) | 4096 produced, 1 dropped; the worker's first packet reads the counter at 4096 | 4097 queued: `.hsUnderLoad` operand 4097, the tail contract predicts 4096 packets | 4096, 1 dropped: exact |
| `e_ring_carry` | …, `wg_flood` 536 + 1 (537 sends), `wg_down`, `wg_up`, `wg_flood` 4087 + 1 (4088 sends) | second flood: 4087 produced, 1 dropped (slots 528 to 536 carried across the down and up) | 4088 queued | 4087, 1 dropped: exact |

The first is the handshake twin of `w7_ring_fresh_1024`; the second of
`w7_ring_batch_clear` and `w7_ring_wrap` together (the batch rule, the
wrap and the carry across `wg_stop` in one flood). The first stage is 537
(536 invalid and the leading valid), not 521 and not 25: 521 = 9 mod every
power of two from 16 to 512, so a 521-packet drain carries nine slots at
batch 32 as well, while 537 = 33 × 16 + 9 carries nine at batch 16 and 25
at batch 32 (4071 produced instead of 4087); and 25, the probes' first
stage, fails in the check for a reason the probes could not show
(section 8, the build): the comparison child reruns the trace in the
coverage child's boot, and the kernel-global `last_under_load`
(receive.c:100) the coverage child's second flood left behind makes a
below-threshold first packet read the decay clock (:117) in the
comparison child only, a record the mirror cannot predict. It is the leak
chunk isolation keeps between traces (`evaluator/check.py`,
`chunk_traces`), here between the two children of one trace; a first
stage under load from the queue depth reads the clocks the mirror predicts
in both children. The `wg_down`/`wg_up` between the stages checks
decision 13.4 (no reinit at `wg_stop`) differentially at a cost of 0.25 s
of the trace budget (section 8). The two traces reject a list mirror in
two independent ways: the operand at `receive.c:112` (`.hsUnderLoad`, the
remote comparison stream) and the tail's predicted length.

The sentinel set gains one mutant, run once and reported in the commit, then
kept only if it replaces a weaker sentinel: the batch rule at 1 instead of
16 on the handshake ring. `e_ring_carry` rejects it: with the batch at 1 the
first stage leaves no carry, so the second flood of 4088 fits the ring
whole (4088 produced, none dropped) against Linux's 4087, one tail packet
too many (the contract predicts an under-load read where the kernel's
packet, one counter lower, read the decay clock) and the counter 4088
against 4087 at :112. `e_ring_full` does not (a fresh ring takes 4096 at
any batch). A batch-32 mutant (`SMP_CACHE_BYTES` 128) is rejected the same
way (4071 against 4087). Run once at the build (B1-M1, commit 5fcac3f, s4):
`e_ring_carry` rejected, `hidden_mismatch`, "operation 6: tail packet 3575
at counter 512: expected the under-load clock read (site 130), found site
6" (the mutant's tail runs one counter ahead of the kernel's); `e_ring_full`
agreed under the mutant; the mutant reverted, not kept.

## 8. The probes [AGENT, 2026-10-15, Linux only, s4, no mirror]

Both read the hidden record stream: kinds 300/301 are section start and
stop (the NET_RX vector's at one call site, the worker's at another), 208
the 8-byte clock reads at `receive.c:115` (under load) and :117 (the
decay), 302 the worker's `cond_resched` yields. Packets consumed = clock
reads, one per packet (section 5). Every flood opens one NET_RX section
per send plus one that carries no records, then one worker section after
them all; "every send reached `wg_packet_receive`" is inferred from
consumed plus the predicted drops equalling the sends, not measured.

**Probe 1** (four traces, one boot, the first form of the traces with
trailing `wg_observe`/`wg_get`; `.tmp/b1-probe/probe.py`, output
`.artifacts/b1-probe/run-1`):

| trace | sends | consumed (under load + decay) | dropped at produce | yields |
| --- | --- | --- | --- | --- |
| `e_underload_cookie` | 521 | 10 + 511 = 521 | 0 | 0 |
| fresh ring, 4097 | 4097 | 3585 + 511 = 4096 | 1 | 9 |
| after a 521 drain, 4088 | 4088 | 3576 + 511 = 4087 | 1 | 8 |
| over, 4201 | 4201 | 3585 + 511 = 4096 | 105 | 7 |

The comparison child failed each big flood with `empty_or_full_kcov`
before writing the operation's rows (section 6); every big-flood figure
above is the coverage child's. The coverage child's `since_up` was 2.93 s,
3.33 s and 2.86 s against 1.06 s for the cookie trace, with the trailing
operations included.

**Probe 2** (the committed forms of section 7, a variant without the
`wg_down`/`wg_up`, and the cookie trace; one boot; the task comparison
area doubled in the guest for the run only; `.tmp/b1-probe/probe2.py`,
output `.artifacts/b1-probe/run-2`; the box was running a suite and a B3
measurement at the time):

| trace | child | `since_up` | flood | consumed | dropped | drain (coarse clock span) | yields | task words / remote words |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `e_ring_full` | pc | 0.66 s | 4097 | 3585 + 511 = 4096 | 1 | 32 ms | 8 | 2.32 M / 1.42 M |
| `e_ring_carry` | pc | 1.09 s | stage 1: 25 | 25 | 0 | 0 ms | 0 | 14 K / 10 K |
| | | | stage 2: 4088 | 3576 + 511 = 4087 | 1 | 28 ms | 8 | 2.32 M / 1.42 M |
| `e_ring_carry_plain` (no down/up) | pc | 0.84 s | stage 2: 4088 | 4087 | 1 | 28 ms | 8 | 2.32 M / 1.42 M |
| `e_underload_cookie` | pc | 1.02 s | 521 | 10 + 511 = 521 | 0 | 4 ms | 0 | 0.30 M / 0.18 M |
| `e_underload_cookie` | cmp | 1.61 s | 521 | 521 | 0 | 4 ms | 1 | 180 K / 100 K records |

Read from the table:

- **The batch is 16 and the carry is physical**: 25 consumed, then 4087 of
  4088 produced (nine carried slots, 25 = 16 + 9); batch 32 would have
  given 4071. The carry survives `wg_down`/`wg_up` (the C's `wg_stop` does
  not touch the cursors), at a cost of 0.25 s.
- **Time, coverage child**: 0.66 s and 1.09 s against the 4.5 s bound
  (section 11). The comparison child's time is **not measured** for the
  big floods: in probe 2 it ran each flood to completion (4099 and 4117
  sections opened, none dropped) and was then killed by the block-table
  overflow of section 6, before its rows and its timing row. Projected
  from the cookie trace's ratio (1.61 against 1.02 s, 1.6; about 2.3 once
  the fixed waits are taken out), the comparison child lands at about 1.1
  to 1.5 s on `e_ring_full` and 1.7 to 2.5 s on `e_ring_carry`, with the
  flood's post-processing (the dedup passes over 1.4 M task and 0.8 M
  remote records) after the last timing check, since the trace ends at
  the flood.
- **The worker's drain inside the flood's 100 ms wait**
  (`QUEUE_WAIT_US`, `guest.c:72, 2614`): 32 ms and 28 ms in the coverage
  child, quantised by the 4 ms coarse clock (`CONFIG_HZ=250`); the cookie
  trace's drain is the same 4 ms in both children, so the comparison
  child's drain is expected near the coverage child's. A margin of about
  3, host-load dependent: an overrun leaks the worker section into no
  operation and `Env.flood` fails closed. The comparison child's drain
  is measured in probe 3 below.
- **The remote comparison count** in the comparison child: measured in
  probe 3 below (the projection from the cookie trace was 783 K).

After probe 2 the twin traces were feasible on every axis measured (the
coverage child's time, the memory, the ring's behaviour, the first stage
at 25) and not yet shown on the comparison child's time, remote count and
drain, which the block-table overflow had cut off.

**Probe 3** (the two committed forms only; one boot; the task comparison
area doubled and `cmp_block` sized by it in the guest for the run only,
plus a `/proc/meminfo` readout before the task area and at the end of
each child, outside every window; `.tmp/b1-probe/probe3.py`, output
`.artifacts/b1-probe/run-3`; the box was running a full check and the
sentinels at the time):

| trace | child | `since_up` | flood | consumed | dropped | drain | task / remote comparison records | vmalloc at end | free at end |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `e_ring_full` | pc | 0.66 s | 4097 | 4096 | 1 | 28 ms | (2.32 M / 1.42 M coverage words) | 100,560 kB | 120,744 kB |
| `e_ring_full` | cmp | **0.67 s** | 4097 | 4096 | 1 | **28 ms** | **1,411,041 / 764,762** | **133,392 kB** | **76,816 kB** |
| `e_ring_carry` | pc | 1.02 s | 25, then 4088 | 25, then 4087 | 0, then 1 | 24 ms | (coverage) | 100,560 kB | 119,508 kB |
| `e_ring_carry` | cmp | **1.21 s** | 25, then 4088 | 25, then 4087 | 0, then 1 | **28 ms** | **1,407,912 / 763,008** | **133,392 kB** | **78,592 kB** |

Both children completed both traces; the host then rejected the run on
its merged comparison bound (section 6), the one host line the change
must raise. Read from the table:

- **Time, comparison child**: 0.67 s and 1.21 s against the 4.5 s bound,
  margins of 6.7 and 3.7, on a loaded host; the comparison child costs
  2 to 19 percent more than the coverage child here, not the 1.6 of the
  cookie trace, since the trace ends at the flood and the flood's
  post-processing falls after the last timing check.
- **Drain**: 28 ms in both children against the 100 ms wait, a margin of
  3.6 (the coarse clock quantises to 4 ms).
- **Remote comparison count**: 764,762 of 1,048,575 (margin 1.37); the
  task comparison count 1,411,041 of the doubled 2,097,151 (margin 1.49).
- **Memory**: the areas peak at 128 MiB (`VmallocUsed` 133,392 kB) in the
  comparison child with 75 MiB free.
- **Console**: the comparison child prints about 3 MB per big flood (the
  remote comparison row 1.40 MB, the task row 0.78 MB, the records
  0.73 MB), after the timing check; each twin is a chunk of its own, so a
  chunk's output stays well inside the 16 MiB limit.

So: the twin traces **exist at the named sizes**: the task comparison
area at 8 M words, `cmp_block` at the task area's size (or not written for
the task area), the remote area unchanged, the host's merged comparison
bound at 3,145,725. Three probes, three limits (the area, the table, the
host bound), each found by the run that hit it, and the third run clean
on every axis. The build then found a fourth thing the probes could not:
with a 25-packet first stage the check's comparison child, which reruns
the trace after the coverage child in the same boot, reads a decay clock
the coverage child's run left armed (section 7); the committed first
stage is 537, with the same nine carried slots.

## 9. Out of scope (fail-noisy), and why

- `rng_is_initialized` false (:552): the guest waits for the RNG, as today.
- The producer with the counter above 2048 (`.rxQueueBusy` true):
  `unsupported` with the corrected reason (4.3, option B); reachable only
  inside a flood, whose producers `Env.flood` summarizes.
- `wg_stop` with messages queued for a worker that has not run: `unsupported`
  as today (its timing), now tested on `.empty`.
- `wg_batch` cannot reach the ring's capacity (`BATCH_MAX` 1025,
  `harness/guest.c`): a batch of handshake injects stays well under 4082,
  so F10's "more than 4081 injects" route is the flood's, not the batch's.
- The merged-injection control's slot (section 5): a negative control only.

## 10. Proof-tree frames touched

The ring's type changes, the flood's shape changes (section 5), the tail
contract's signature changes (it takes the predicted tail), and the fuel
changes (4.2). `git grep` over `Leanux/Proofs` for `handshakeQueue`,
`receiveStep`, `handshakeReceiveWorker`, `floodTailEffect`,
`packetReceive`, `wgStop`, `wgDestruct`, `MAX_QUEUED_INCOMING_HANDSHAKES`,
`floodLogged`, `Env.flood` on the three trees:

**`main` (ca6b22e), 11 files:**

- `Logged/Operations.lean`: :238-239 (`requireDrained` on `isEmpty`),
  :255-298 (`floodLogged`: the four steps of section 5), :301-303
  (`floodLogged_erases`) and its uses :334, :365, :416; note that this
  copy already lags `Env.flood` (no `family`, no `floodExact` branch), so
  the repair lands on an existing lag.
- `Logged/Scheduler.lean` :49 (`workerIterLogged` over `receiveStep`), :87,
  :113 (`isEmpty` → `empty`).
- `Logged/Syscalls.lean` :30, :49 (`floodLogged`'s dispatch and erasure).
- `Logged/Workers.lean` :107-113 (`handshakeReceiveWorkerLogged`: the fuel
  and its erasure through the step's consume).
- `WG/Keypairs/Evolution/Operations.lean` :18-19 (the worker's evolution
  head), :42 (`floodTailEffect`'s head: new signature), :119-121
  (`floodLogged_evolves`: the tail's consume needs its own lemma).
- `WG/Keypairs/Evolution/Scheduler.lean` :54-63 (`receiveStep_ordinary`,
  `handshakeReceiveWorkerLogged_evolves`), :106.
- `WG/Keypairs/Evolution/Syscalls.lean` :133.
- `WG/Keypairs/Frames/Env.lean` :29-35 (`floodTailEffect_sameSnapshot`,
  `_spec`: the signature).
- `WG/Keypairs/Frames/EnvWorkers.lean` :73-80 (`handshakeReceiveWorker_ordinary`,
  `_spec`).
- `WG/Keypairs/Frames/WGDevice.lean` :31-39 (`wgStop_ordinary`, `_spec`,
  `wgDown`), :126-149 (`wgDestruct_ordinary`, `_spec`, `wgDelete`).
- `WG/Keypairs/Frames/WGMore.lean` :460-465 (`packetReceive_ordinary`: the
  full test; the new decision too under option A), :611.
- Not touched: `ReplayWindow/Counterexamples.lean` (the decrypt ring only).

**`proofs/campaign` (campaign 1, b1ec9e8), 28 files:** the 11 above (with
`floodLogged` already carrying `family` and `floodExact` there,
`Logged/Operations.lean:284-350`), plus:

- `Framing/EnvOperations.lean` :78-85 (`floodTailEffect_sameKernel` by
  `mvcgen` over the loop: the signature and the per-packet walk).
- `WG/Lifetimes/ReceiveWorker.lean` (`popHandshakeQueue` as `drop 1` :9-10,
  `ReceiveQueueContracts.pop` :16, `receiveStepPrefix` matching on the list
  :32-39, the fuel :47-49, proofs by `cases d.handshakeQueue` :55, :79):
  rewritten over `consume`.
- `WG/Lifetimes/ReceiveIngress.lean` :12 (the append), :50-60 (the copy of
  `packetReceive`: the length test and the busy arm), its erasure :84-86
  and preservation :123-130.
- `WG/Lifetimes/BatchActivation.lean` :16, :29 (`.length` occupancy).
- `WG/Lifetimes/BatchAudit.lean` :48, :186-188 (the fuel), :207.
- `WG/Lifetimes/BatchScheduler.lean` :19, :97, :133.
- `WG/Lifetimes/DeviceControls.lean` :74, :77, :156 (`wgStopPrefix`: the
  emptiness test and the reset).
- `WG/Lifetimes/DeviceLifecycle.lean` :19, :22 (`wgDestructPrefix`).
- `WG/Lifetimes/EnvRemainingCalls.lean` :55 (`Env.flood`'s arity, unchanged
  unless a parameter is added).
- `WG/Lifetimes/EnvTrafficAudit.lean` :81, :85, :99, :128-136 (the flood's
  audit copy: the four steps), :150-171, :206-207 (its erasure).
- `WG/Queues/RxRingHandshake.lean` :291-298 (`receiveStep_cell` by `mvcgen`
  over the list match).
- `WG/Queues/RxRingScheduler.lean` :14-17 (`receiveIter_cell`).
- `WG/Queues/SourceScheduler.lean` :44, :64.
- `WG/LifetimeSafety/Statements.lean` :1407-1436 (the worker erasure and
  preservation statements; the docstring's fuel), under the proof gate.
- Unchanged in content, dependent by name: `WG/Cookies/Gate.lean` :17-43,
  `WG/Cookies/Load.lean` :10-32, `WG/FloodResistance/Statements.lean`
  :15-27 (the counter and the constant's name only);
  `WG/DeliveryOrder/Statements.lean` (generic over `PtrRing`; its ring
  lemmas apply to the handshake ring unchanged, a small gain).

**`proofs/campaign-2` (campaign 2, e56156e), 12 files:** the 11 of `main`,
plus `WG/Progress/BatchBacklog.lean` :49 (`handshakeQueue.length` in a
backlog tuple decided by `decide +kernel`: `.count`).

Both campaigns carry under the lag-and-repair rule; the integration record
names the lag. The plan's cost note ("B1's is the next largest, since the
handshake ring's frames change type") stands, and campaign 1's carry is
about a day, not hours: the list-shaped proofs in `Lifetimes/ReceiveWorker`,
`Queues/RxRingHandshake` and the audit copy of the flood are rewritten,
not retyped.

## 11. Risks [AGENT]

- **The trace bound.** The guest fails a trace whose time from its first
  `wg_up` to the end of its last operation exceeds `REKEY_BOUND_NS` = 4.5 s
  (`guest.c:110, 2640-2645`), in each child separately; the mirror's
  `TRACE_BOUND_MS` (`Env.lean:134`) is the same bound. Measured on a
  loaded host: the coverage child at 0.66 s and 1.02 s, the comparison
  child at 0.67 s and 1.21 s (section 8), margins of 3.7 to 6.7. TCG guest
  time follows host time ([the contended-host note](2026-10-06-contended-host.md)):
  the margin is what absorbs the load, and a bound failure is an
  infrastructure outcome, rerun at most once under the standing rule.
- **The flood's 100 ms wait.** The worker's drain of 4096 packets is
  28 ms in both children (section 8), a margin of 3.6 that a loaded host
  eats into. An overrun is a fail-closed `Env.flood` outcome, not a wrong
  verdict. If the claim point shows the margin thin, the flood's wait
  becomes a trace field like `wg_batch`'s `wait_ms` (a guest and
  `trace.py` change) at the cost of trace time.
- **The remote comparison margin** is 1.37 at 4097 sends; a kernel
  rebuild that adds comparisons on the receive path narrows it. The
  per-stream full check in the guest is the guard.
- **The tail contract's exactness at the threshold.** The per-packet rule
  of section 5 must match the C at 512 and at the expiry; the boundary
  traces (`e_underload_511/512/513`) and `e_underload_decayed` are the
  regression set, and the two probes' counts (10 + 511, 3585 + 511,
  3576 + 511) are its first check.
- **Carry across operations.** The ring's carried slots now persist across
  `wg_down`/`wg_up` and every later operation, as the C's do (measured).
  No corpus trace reaches the capacity after a drain except `e_ring_carry`,
  so no silent dependence on the old reinit is expected; the full check at
  the claim point is the test.
- **The flood rework is the delicate part.** Steps 1 to 4 of section 5
  and the per-packet contract are new control flow in the environment,
  with a Logged copy and an audit copy on campaign 1; the crypt-ring
  precedent (4b9dcaf, 177 lines) had nothing of the kind.

## 12. Estimate

In WU (one WU is WireGuard, about three weeks, [the scout](2026-10-12-kernel-scout.md)):

- the mirror change (4.1 to 4.4, the fuel, `wg_stop`), the environment
  rework (section 5: the producer loop, the bounded leading run, the tail
  consume, the per-packet contract, `floodExact`) and the Logged copy on
  `main`: about 0.07 WU, a day and a half; the environment rework is the
  part that is not mechanical;
- the comparison-capacity change (section 6: guest, host bound, tests,
  about 40 lines), the two traces, the one-off mutant (section 7): about
  0.03 WU, half a day to a day; the probe that showed the traces exist is
  done (section 8), so no boot of uncertain outcome remains;
- the claim point and controls: the usual hour at eight slots, plus the
  under-load chunks;
- campaign 1's carry: about a day (section 10); campaign 2's: hours.

About 0.10 WU with the traces, three days; about 0.07 WU, two days,
without them; plus the carries. Order: the mirror change on `main`'s tree,
then the capacity change with its tests, then the traces and the mutant.

## 13. Decisions

For the user:

1. **The comparison-capacity change for the twin traces** (section 6): a
   second guest constant for the task comparison area and its full check,
   `cmp_block` sized by it or dropped for the task area, a second host
   bound raised to the sum of the two streams' limits with every
   per-stream guard kept, two tests extended; no kernel change, no
   identity change, no guest-memory change. **Settled by probe 3: the twin
   traces are feasible at these sizes.** Measured on a loaded host, in
   the comparison child: 0.67 s and 1.21 s of the 4.5 s bound, a 28 ms
   drain of the 100 ms wait, 764,762 remote comparison records of
   1,048,575 and 1,411,041 task records of the doubled 2,097,151, the
   areas at 128 MiB with 75 MiB free; the ring's behaviour exact at a
   25-packet first stage, across a `wg_down`/`wg_up`. The alternative is
   to leave the capacity arms at unit-level evidence (4.4) and the
   strengthened contract, and keep the corpus at floods of 520.
   Recommended: the change; the two traces are the only differential
   evidence of the handshake ring's occupancy, and the change is about 40
   lines in the harness with no open question left.

Tactical [AGENT], stated for the record:

2. The `> 2048` arm keeps its `unsupported`, with the reason corrected to
   the build fact (4.3, option B); option A is written down for the day
   the flood's producer runs through `packetReceive`.
3. The flood tail contract simulates the tail packet by packet over the
   predicted length (section 5).
4. `wg_stop` leaves the ring's cursors as the C does; the field is not
   reinitialised below the device's own lifetime; `e_ring_carry` checks it
   across a `wg_down`/`wg_up`.
5. `MAX_QUEUED_INCOMING_HANDSHAKES` moves to `Types.lean` under its name.
6. The worker's fuel is the capacity plus one, in every copy (4.2).
7. The twin traces end at their last flood, and the carry twin's first
   stage is 537, under load, since a below-threshold first stage reads a
   decay clock the mirror cannot predict in the comparison child (section
   7).

## 14. Artifacts

`.tmp/b1-probe/` (the three probe scripts and their logs) and
`.artifacts/b1-probe/` (`run-1`, `run-2`, `run-3`: `boot.log`,
`hidden.jsonl`, `probe.json`) in the design worktree: ephemeral, deleted
with the worktree. The guest changes of probes 2 and 3 (the task
comparison area doubled; for probe 3 also `cmp_block` sized by it and the
`/proc/meminfo` readout) were reverted after each run and are not on the
branch. The commands, for a rebuild (probes 2 and 3 need their guest
change applied by hand first):

```sh
LEANUX_SHARED_ROOT=/home/dev/projects/lean-ux-proto \
LEANUX_KERNEL_DIR=/home/dev/projects/lean-ux-proto/.artifacts/kernel-net-choice-s4 \
capped -- scripts/in-bundle python3 .tmp/b1-probe/probe.py --out .artifacts/b1-probe/run-1
LEANUX_SHARED_ROOT=/home/dev/projects/lean-ux-proto \
LEANUX_KERNEL_DIR=/home/dev/projects/lean-ux-proto/.artifacts/kernel-net-choice-s4 \
capped -- scripts/in-bundle python3 .tmp/b1-probe/probe2.py --out .artifacts/b1-probe/run-2
LEANUX_SHARED_ROOT=/home/dev/projects/lean-ux-proto \
LEANUX_KERNEL_DIR=/home/dev/projects/lean-ux-proto/.artifacts/kernel-net-choice-s4 \
capped -- scripts/in-bundle python3 .tmp/b1-probe/probe3.py --out .artifacts/b1-probe/run-3
```

## 15. Review dispositions [AGENT, fork of the coordinator, v2]

The review's 13 findings, one by one. "Fixed" means the note now says what
the finding asked, at the section named.

1. **The 4.5 s trace bound** (blocking for the evidence plan). Fixed and
   measured as far as one boot allowed: the traces now end at their last
   flood and the carry twin's first stage is 25 (section 7); the coverage
   child is at 0.66 s and 1.02 s and, after the block table was sized,
   the comparison child at 0.67 s and 1.21 s on a loaded host (probe 3,
   section 8); decision 13.1 is settled on the measured numbers, and the
   bound is named in section 11.
2. **The worker over the tail** (blocking). Fixed: section 5 adopts the
   review's shape, produce the whole batch, `workerIter` exactly `leading`
   times, the tail consume with the contract, one final `receiveStep`
   required `false`; the Logged and audit copies follow (section 10).
3. **The fuel.** Fixed: capacity plus one, checked against the C's unbounded
   loop (section 2) and `workerLoop`'s iteration count (4.2), with every
   copy named, including the statement file's docstring; decision 13.6.
4. **The trylock.** Fixed: the reason is the compile-time constant
   (`spinlock_api_up.h:75` under the two unset options, section 2); the
   decision's sides are corrected (`whenTrue = []`, `whenFalse = [(556,
   557)]`, the stop on the true side) and the coincidence with
   `.rxQueueBusy`'s span stated; both options are written out with the
   cost, and the recommendation changes to keeping the stop with a correct
   message (4.3, decision 13.2).
5. **The tail contract.** Fixed: a per-packet simulation over the counter
   and the running `last`, with the expiry case followed and never a
   failure, the yields dropped between packets, `stop` required after the
   last packet (section 5); the probes' counts are its first check.
6. **The frames.** Fixed: section 10 lists 11 files on `main`, 28 on
   campaign 1 (b1ec9e8 now, not ecb5661) and 12 on campaign 2 (e56156e now,
   not 8d841ba), from `git grep` on each tree, with the constant's name
   kept (4.1) and the carry re-estimated at a day (section 12).
7. **The capacity change's scope and the memory argument.** Fixed: section
   6 names the single `CAPACITY` and every area, table and check it sizes,
   the host's single `KCOV_CAPACITY` and its two tests, the per-stream
   guards that must stay, and the second guest limit probe 2 found
   (`cmp_block`); the memory argument is corrected to `vmalloc_user`'s
   up-front zeroed pages, 96 MiB today and 128 MiB after, measured in
   probe 3 at 133,392 kB of vmalloc with 76,816 kB free;
   `EXPECTED_MAX_USER_WATCHES` and the rate limiter's table are named as
   total-memory quantities, unchanged at `-m 256`; the remote comparison
   count is measured at 764,762 of 1,048,575, and the host's merged bound
   (`linux.py:585, 726-727`) is added to the change's scope after probe 3
   hit it.
8. **What the figures support.** Fixed: the batch is now shown by the
   25-packet first stage (4087, where batch 32 gives 4071) in probes 2 and
   3 and the `#guard` uses the same number (4.4); the committed trace uses
   537 for the reason section 7 gives, with the same carry; the sections are
   read as one NET_RX section per send plus one without records, then the
   worker's, and "every send reached `wg_packet_receive`" is marked as
   inferred (section 8); probe 1's big-flood figures are attributed to the
   coverage child, and probe 2's report keys every row by child.
9. **Mutant arithmetic.** Fixed: at batch 1 the second flood of 4088 is
   produced whole, 4088 against 4087, rejected by the operand and by one
   tail packet too many (section 7).
10. **The drain margin.** Fixed and measured: 28 ms in both children
    against the 100 ms wait, a margin of 3.6, with the mitigation named
    (section 8, section 11).
11. **Citation slips.** Fixed: the ":845 stop drain" is gone (the stop's
    test is `Device.lean:94`, 4.2); the probe script's docstring now names
    the kinds, not the mirror's site ids.
12. **The estimate.** Fixed: 0.11 WU, three to four days with the traces,
    0.07 WU, two days without, plus a day's carry on campaign 1 (section
    12), with the environment rework named as the non-mechanical part.
13. **`wg_down`/`wg_up` in the carry twin.** Adopted and measured: 0.25 s
    of the budget, and the nine carried slots survive it (sections 7, 8;
    decision 13.4).

## 16. The build [AGENT, fork of the coordinator, 2026-10-15]

On `task/design-b1`, in three commits after the note: 676eee9 (the mirror:
sections 4 and 5, the fuel in every mirror copy, option B of 4.3, the
`#guard`), 5fcac3f (the capacity change of section 6 in full, the
generator and the two traces of section 7, the one-off mutant run once)
and this note's update. The proof tree is not edited; the copies the
campaigns repair under the lag rule are the fuel in
`Leanux/Proofs/Logged/Workers.lean:107-109` on `main` and both campaign
branches, campaign 1's `Lifetimes/ReceiveWorker.lean:47-49` and
`Lifetimes/BatchAudit.lean:186-188` and the docstring of
`LifetimeSafety/Statements.lean:1407-1409`, and the ring's type in the
frames of section 10.

Two things the build found that the design did not have:

- **The carry twin's first stage is 537, not 25** (section 7): the check's
  comparison child reruns a trace after the coverage child in the same
  boot, and `last_under_load` (receive.c:100, kernel-global) stays armed
  from the coverage child's second flood, so a below-threshold first
  packet reads the decay clock in the comparison child only. The probes
  ran each trace once per child too, but with other floods before it in
  the same boot, which hid the asymmetry. It is the leak chunk isolation
  already keeps between traces; between the two children of one trace the
  only exact rule is the trace's construction: the first handshake packet
  of a trace that will cross the threshold must itself be under load from
  the queue depth. No kernel or harness change; recorded here as a
  constraint on under-load corpus traces.
- **The host's merged comparison bound** (section 6, found by probe 3 and
  raised at the build).

Validation on the committed tree, on s4 under a loaded box: the five
unit-test modules 124 OK (1 skipped); the `wireguard` suite 263 traces,
1798 operations, 263 agreements, no retries, 34 minutes at eight slots
beside a full check and a sentinel chain (`.artifacts/check/b1-wg-final`,
ephemeral).

### 16.1 The regression at the batch's claim point, and its fix [AGENT, 2026-10-15]

On `int/repr-batch` (B4 then B1 over the landed index-lookup fix) the
claim point's `seccomp` group failed 47 of 267 traces at `output_limit`
("Captured output exceeded 16777216 bytes"), single-trace chunks
included, while the same group had passed in full an hour earlier
without B1. Measured on `s_strict_child` (three seccomp probe
operations), Linux only, one boot each:

| tree | `boot.log` | task comparison rows: records / distinct / bytes per operation |
| --- | --- | --- |
| main de62c9d | 12,582,748 B | 258,654 / 68,761 / 3.52 MB; 344,410 / 87,951 / 4.46 MB; 346,137 / 88,253 / 4.48 MB |
| branch 5fcac3f (area at 8 M words for every trace) | truncated at 16,777,216 B | 384,042 / 101,615 / 5.22 MB; 469,832 / 120,829 / 6.16 MB; the third row cut |
| branch with the per-trace area | 12,537,850 B | 258,581 / 68,709 / 3.52 MB; 342,426 / 87,528 / 4.44 MB; 343,538 / 87,751 / 4.45 MB |

What grew: not a dump proportional to the capacity, not the table, not
the header. Each probe operation's task comparison stream gained about
125,400 records and 32,900 distinct ones, the same on every operation,
and the extra distinct records sit at four program counters: `mm/memory.c:1189`
(`copy_pte_range`, 24,647 of them), :1139 (`copy_pte_range`), :597
(`vm_normal_page`) and `pte_pfn` (`arch/x86/include/asm/pgtable.h:266`),
8,192 to 24,647 each, which is one to three per page of the 8,192 pages
the larger mapping adds. A seccomp probe forks its sandboxed child; the
KCOV task area is a shared `VM_MIXEDMAP` mapping whose page tables `fork`
copies, one comparison with a distinct pfn operand per page, and the
comparison child records that work. The growth is inherent to the mapping
size and a harness artefact of the change: the area is now sized per
trace (above), the seccomp probes' output returns to its former size, and
the flood twins keep theirs. Nothing dropped silently before: every
seccomp row's count was far below the old limit of 1,048,575.
