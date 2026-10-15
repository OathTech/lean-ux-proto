# B1 design review: the handshake queue as a `PtrRing` — 2026-10-15

Independent review [AGENT, reviewer] of
[the B1 design note](2026-10-15-design-b1-handshake-ring.md) at de33b91
(branch `task/design-b1`, from main ca6b22e). Read-only: no guest boot, no
check run; the note's probe output (`.artifacts/b1-probe/run-1`) was
re-analysed, not re-run. Kernel source `.deps/linux` (6.12.110), oracle
config `.artifacts/kernel-net-choice-s4/.config`.

## What holds

The C citations of sections 1 and 2 check out line by line: `device.c:358-359`,
`messages.h:51`, `queueing.c:24-40`, `ptr_ring.h:104-116`, `:158-166`,
`:169-174`, `:247-289`, `:291-303`, `:361-370`, `:474-484`, `receive.c:112-117`,
`:206-218` (`atomic_dec` :215, `cond_resched` :216), `:550-571`, `:585`,
`device.c:130-132` and `:258`. So do the mirror citations (`Types.lean:446`,
`:211-215`; `Receive.lean:36`, `:343-356`, `:465-484`, `:473-476`;
`Device.lean:94-97`, `:271-276`; `Env/Batch.lean:146/223/268/311`;
`Env.lean:772-773`, `:791-848`; `Defs.lean` `floodTailEffect` at :2264;
`check.py:1043-1059`; `guest.c:51`, `:2649-2650`). The batch is 16 on this
config (`CONFIG_X86_L1_CACHE_SHIFT=6`, so 64 * 2 / 8 = 16, not above 2048).
The probe's central figures replicate from `hidden.jsonl`: 4096 consumed
from a fresh ring, 4087 after a 521-packet drain, 4096 at 4201 sends, every
NET_RX section ahead of the single worker section (no NET_RX section opens
after the worker starts, in any of the four floods). The representation
(the crypt rings' `PtrRing`, the counter kept apart, no reinit at
`wg_stop`) is the right one and keeps the thin-layer shape: same-shaped
state, consume and produce at the C's sites, no C memory modelled (a
consumed slot holds a stale value where the C holds a stale pointer; only
occupancy is read).

The findings below are about how the flood environment is reworked, the
evidence plan, and the cost accounting.

## Findings

### 1. The twin traces may not fit the 4.5 s trace bound in the comparison child — blocking (for sections 6, 7 and decision 13.1; not for the mirror change)

The guest fails any trace whose time from `wg_up` to the end of its last
operation exceeds `REKEY_BOUND_NS` = 4.5 s (`harness/guest.c:110`,
`:2640-2645`, `trace_exceeds_rekey_bound`), separately in each child; the
mirror uses the same bound (`Env.lean:134`, `TRACE_BOUND_MS`). The note
never mentions it. The probe's own `timing.jsonl` gives the coverage child
`since_up` 2.93 s (`b1_ring_fresh_4097`), 3.33 s (`b1_ring_carry_4088`),
2.86 s (`b1_ring_over_4200`), against 1.06 s for `e_underload_cookie`. On the
cookie trace the comparison child takes 1.65 s, 1.56 times the coverage
child (more once the fixed waits are subtracted: about 0.6 s of the trace is
`usleep`s, so the comparison child's work is about 2.3 times the coverage
child's). Scaled either way, the comparison child of `e_ring_full` lands
near or above 4.5 s, and `e_ring_carry` (two floods, about 4600 sends) above
it. The comparison child never reached that point in the probe because its
area filled first, so the doubled area alone does not show that the traces
exist; the time bound can then fail them. The flood's post-processing
(deduplicating about 1.4 M task and about 0.8 M remote comparison records)
runs before the next operation, so it counts against the trailing
`wg_observe`/`wg_get` too. The bound also tracks a contended host (TCG guest
time follows host time, `docs/2026-10-06-contended-host.md`).

To settle it: the section 6 probe (doubled area) must also report the
comparison child's `since_up`, on the twin traces in the form they would be
committed, on a loaded host. Shapes that cut time: end each twin trace at
the flood (drop `wg_observe`/`wg_get` and its 0.4 s wait, or keep only what
the margin allows); build `e_ring_carry`'s first stage from a small flood
or about 25 `wg_inject`s rather than 520 + 1 (finding 8 gives a second
reason). If the comparison child still exceeds 4.5 s, the traces do not
exist at this bound, and decision 13.1 should not go to the user as "the
two traces cost a constant". Raising the bound for peerless traces, which
arm no timer, would be a harness and environment change in its own right,
for the user to decide.

### 2. Section 5 does not say how the real worker processes only the leading valids once the tail is in the ring — blocking (design hole in the environment rework)

Today `Env.flood` puts only the leading valids in the list (`Env.lean:837`),
so `WG.handshakeReceiveWorker` stops after them and the summary takes over.
The note puts the whole batch through the ring in the C's order, which it
must, since the C produces every packet before the worker runs and the full
test depends on that order. But it then says that "the leading valids run
through the real worker as today, consuming from the ring", and then that
the summary consumes `produced - leading`. The real worker loops
`receiveStep` until the ring is empty (`Receive.lean:358-360`,
`Defs.lean:1789-1793`), so it would consume the tail through
`receiveHandshakePacket` (that is `floodExact`, and the summary is gone).
The alternative of producing the tail after the leading valids are consumed
gets the wrong full outcomes in general (consumed slots, and with 16 or more
leading valids a batch clear, sit between the produces).

Proposed shape, for the note to adopt or replace: produce the whole batch
in the C's order (fail closed if a leading valid is dropped); run
`workerIter .receiveWorker none WG.receiveStep (nestedResched …)` exactly
`leading` times; run the tail summary, which consumes the rest with
`PtrRing.consume`; then one `WG.receiveStep` on the drained ring, so the
C's final empty poll (`.workerConsumed false`, receive.c:212) comes after
the tail as it does in the C, and not after the leading valids as today.
The Logged copy (`floodLogged`) and its erasure follow the same shape.

### 3. The worker's loop bound is one short for a full ring — should-fix

The note keeps `handshakeReceiveWorker`'s bound at
`MAX_QUEUED_INCOMING_HANDSHAKES` (section 4.2). `workerLoop` runs at most
`bound` iterations and then stops with `invariant drained`
(`Defs.lean:1789-1793`). A run that drains a full ring needs 4096 consuming
iterations plus the empty poll: 4097. With the ring at capacity (the
`floodExact` path on `e_ring_full`, or any later path that runs the real
worker over a full ring) the mirror would stop with "the handshake queue
did not drain" where the C ends normally. It fails noisily, but it is wrong.
The fuel should be capacity + 1. The same bound is copied in
`Logged/Workers.lean:107-109` (main and both campaigns) and in campaign 1's
`Lifetimes/ReceiveWorker.lean:47-49`, and is named in campaign 1's
`LifetimeSafety/Statements.lean:1407-1409` ("the 4096-step exhaustion
Stop"), which is a statement file under the proof gate.

### 4. The trylock decision: the conclusion is sound, the stated reason is not the operative one, and the spans and stop side are inverted — should-fix

On this oracle `CONFIG_SMP` and `CONFIG_DEBUG_SPINLOCK` are both unset, so
`spin_trylock_bh` goes through `spinlock_api_up.h:75`,
`#define _raw_spin_trylock_bh(lock) ({ __LOCK_BH(lock); 1; })`
(`spinlock.h:312-314` selects that header, `:409-411` is the wrapper). The
trylock is the constant 1 at compile time, whatever the context. The note's
argument (softirq context, softirqs do not nest) is weaker and not needed;
cite the macro and the two config options instead. That makes the claim a
build fact, which is what an `unreachable` stop should rest on. No arm is
hidden.

Section 4.3 then reads: "constant-false decision `rxTrylockFailed` … true
span (556, 557) …, false span empty … stopping `unsupported` … on its false
side". By `Decision.lean`'s convention (`d label file line whenTrue
whenFalse`, :588, with `rxRngNotReady` at :1146 as the model), a decision
named "failed" that is constantly false has the failure arm as its true
side. So it needs `whenTrue = []` (the arm has no line of its own), `whenFalse
= [(556, 557)]`, and the `unsupported` on the **true** side. As written, the
mirror would stop on every busy produce. Since the compiler folds the
constant, the false span's witnesses coincide with `.rxQueueBusy`'s true
span (555-558). That is harmless but worth stating.

The note says so itself, but it is worth weighing: `packetReceive` never
sees the counter above 2048. Only `Env.flood` reaches it, and the flood
produces through its own loop. So the new decision is never exercised by
any trace or unit test, while it touches `kcov.json`, `WGMore.lean`'s
`packetReceive_ordinary` and campaign 1's copy in
`Lifetimes/ReceiveIngress.lean:50-60`. Keeping the `unsupported` with a
corrected message ("unreached: the counter exceeds 2048 only inside a
flood, whose producers `Env.flood` summarizes; the trylock is the constant
1 on this build") would be equally honest and cost nothing in proofs.
Either choice is defensible; the note should make it with the cost in view.

### 5. The strengthened tail contract must be a per-packet simulation, not an expected count — should-fix

Section 5 says the contract "takes the expected count and fails closed when
the records are fewer or more". After a decay read finds the decay expired,
`last_under_load` is cleared (receive.c:118-119) and every later tail packet
reads no clock and leaves no record. A tail can therefore legitimately have
fewer clock records than packets, and the packets after the expiry are
invisible in the stream. The note's own three cases describe this, but
"expected count" does not implement it. For the rule to be exact and fail
closed, the contract should walk the tail packet by packet over the counter
values (`produced` down) and the running `last`: for each packet, require
exactly the predicted site next (under-load read while the counter is at or
above 512; decay read while below with `last` set, the clock value deciding
the clear; nothing otherwise), dropping only the `resched` and cut records
between packets, and require `stop` right after the last packet. In the
probe the tail's decay phase took about 4 ms of coarse clock, so expiry does
not occur in these traces. The rule still has to be right for slow hosts,
where expiry inside the tail is a scheduling outcome that must not become a
failure (AGENTS.md, contended host).

### 6. The list of proof-tree frames touched is incomplete — should-fix

`git grep` over `Leanux/Proofs` (handshakeQueue, receiveStep,
handshakeReceiveWorker, floodTailEffect, packetReceive, wgStop):

- **main (ca6b22e), missing from section 10:** `WG/Keypairs/Frames/Env.lean:29-35`
  (`floodTailEffect_sameSnapshot/_spec`: the contract's signature changes
  with the expected tail), `WG/Keypairs/Evolution/Operations.lean:18-19, 41-42`
  (the flood's head lemmas; the new tail consume needs its own),
  `WG/Keypairs/Frames/WGDevice.lean:31-39` (`wgStop_ordinary`; `wgDestruct`
  likewise), `WG/Keypairs/Frames/WGMore.lean:460-465` (`packetReceive_ordinary`:
  full test, and the new decision if finding 4 keeps it),
  `WG/Keypairs/Frames/EnvWorkers.lean:73-80`. Also: main's `floodLogged`
  (`Logged/Operations.lean:255`) already lags `Env.flood` (no `family`, no
  `floodExact` branch), so the B1 repair lands on top of an existing lag.
- **proofs/campaign (ecb5661): far more than "the same four".**
  `Lifetimes/ReceiveWorker.lean` (`popHandshakeQueue` as `drop 1`,
  `receiveStepPrefix` matching on the list, and proofs by `cases
  d.handshakeQueue`, all rewritten), `Lifetimes/ReceiveIngress.lean:50-60`
  (a copy of `packetReceive` with the length test and the busy arm),
  `Lifetimes/BatchActivation.lean:16, 29` (`.length` occupancy),
  `Lifetimes/BatchAudit.lean:48`, `Lifetimes/BatchScheduler.lean:19, 97, 133`,
  `Lifetimes/DeviceControls.lean:74`, `Lifetimes/DeviceLifecycle.lean:19`,
  `Lifetimes/EnvTrafficAudit.lean:81, 128-171` (the flood's audit copy),
  `Queues/RxRingHandshake.lean:291-298` (`receiveStep_cell` by `mvcgen`
  over the list match), `Queues/RxRingScheduler.lean:14-17`,
  `Queues/SourceScheduler.lean:44, 64`, `Framing/EnvOperations.lean:78-85`
  (`floodTailEffect_sameKernel`), and `LifetimeSafety/Statements.lean:1407-1436`
  (finding 3).
- **proofs/campaign-2 (8d841ba):** the five main files above as well as the
  four the note names.
- The constant's move is safe only if it keeps its name in `Leanux.WG`:
  campaign 1's `Cookies/Gate.lean:18-43` and `Cookies/Load.lean:10-20`
  unfold `MAX_QUEUED_INCOMING_HANDSHAKES` by name.

Under the lag-and-repair rule this does not gate the mirror change, but the
plan's carry cost for B1 on campaign 1 is closer to a day than to hours.
The integration record has to name the lag.

### 7. The comparison-area change is wider than "a constant", and the memory argument is wrong — should-fix

Scope: `CAPACITY` (`guest.c:51`) is one constant for the task area (:1935,
:1939), the remote area (:1447-1451, and its `remote_size`, which also sizes
the kernel's per-section area for task-context remote sections,
`kernel/kcov.c:903-915`), the child area (:2065-2066), the guest's
remote-record tables (`cmp_block`, `distinct`, `ranges`, :464-505) and both
full checks (:2649, :2675). On the host, one `KCOV_CAPACITY`
(`harness/trace.py:172`) bounds every stream (`harness/linux.py:717, 726`,
`evaluator/protocol.py:325`), and `harness/test_trace.py:524` and
`evaluator/test_evaluation.py:147` pin it. To double only the task
comparison area takes a second constant, per-stream host bounds and their
tests. These are instrument guards on the trust surface, so the change must
keep a per-stream full check for every area, which a single raised host
bound would loosen.

Memory: `KCOV_INIT_TRACE` allocates with `vmalloc_user` (`kcov.c:718`),
which is `__GFP_ZERO` (`mm/vmalloc.c:4063-4069`): the pages are committed
and zeroed at once, not "touched lazily" (section 11). The comparison child
of a flood already holds about 96 MiB of KCOV memory, not 64: task 32,
remote 32, and the 32 MiB area the worker's remote section allocates (and
`kcov_remote_area_put` caches). After the change it holds about 128 MiB,
plus the guest's touched static tables (`dedup_table` 16 MiB, `distinct`
16 MiB, `bulk_out` 16 MiB, partly touched), in 256 MiB. It probably fits,
but the note's figures do not show it. The probe settles it; a shortfall
fails noisily (`initialize_kcov` returns ENOMEM).

Oracle behaviour: no kernel change and no identity change. The
memory-derived quantities the mirror depends on are read from total, not
free, memory: `max_user_watches` at boot (`harness/linux.py:146-157`, guarded
by `EXPECTED_MAX_USER_WATCHES`, which a rebuilt initramfs can move: re-check
it after the guest rebuild) and the rate limiter's table size from
`totalram_pages()` (`ratelimiter.c:173-177`). I found no trust-surface
property weakened, provided the per-stream guards stay.

Remote comparison area: unmeasured at 4096. The cookie trace's flood had
99,674 remote comparison records for 521 packets; linear scaling gives about
0.78 M of the 1.05 M-record limit, a margin of about 1.3 times. The note's
"the remote area unchanged" rests on that extrapolation, which it should
state and the probe should measure.

### 8. The probe's figures support less than the note draws from them — should-fix

- **"The batch is 16" is not shown.** 521 = 9 mod every power of two from
  16 to 512, so a batch of 32, 64 … 512 also carries nine slots and also
  gives 4087. The probe and `e_ring_carry` rule out batches 1 to 8, not 32.
  A batch-32 mutant (for example `SMP_CACHE_BYTES` 128) passes both twin
  traces. A first stage of n consumed with n mod 32 ≥ 16 discriminates: 25
  (or 537) carries 9 at batch 16 and 25 at every larger power of two. A
  25-packet first stage also shortens `e_ring_carry` (finding 1). The unit
  `#guard` of section 4.4 can use the same n.
- **Sections.** `hidden.jsonl` has 4098 section starts in `handle_softirqs`
  and one in `process_one_work` for 4097 sends (`sections.jsonl`: 4099
  opened). Every flood, the cookie trace included, has one NET_RX section
  more than it has sends, and that section carries no records. So
  "sections opened = one `net_rx` per send plus one worker section" is a
  misreading, and "every send reached `wg_packet_receive`" is inferred (from
  consumed plus the predicted drop equalling the sends), not measured.
- **The comparison child's records.** For the three big floods the
  comparison child failed at the flood operation before writing any of that
  operation's rows: there is no comparison-mode hidden or remote row for it
  in `hidden.jsonl`, and `probe.json` keys rows by operation only, so the
  coverage child's rows stand in. Every big-flood figure is the coverage
  child's. Its remote comparison count and timing (findings 1 and 7) are
  unknown.

### 9. Mutant arithmetic — note

Section 7: with the batch at 1, `e_ring_carry`'s first stage leaves no
carry, and the second flood of 4088 fits a 4096-slot ring whole: 4088
produced, none dropped, not "4096 produced". It is still rejected (counter
4088 against 4087 at receive.c:112, and one tail packet too many).

### 10. Worker drain margin inside the flood's wait — note

The flood operation waits `QUEUE_WAIT_US` = 100 ms (`guest.c:72, 2614`), and
the worker section must close inside the operation or `Env.flood` fails
closed. From the coarse clock records, the coverage child's worker took
about 32 ms for 4096 packets (8 ms for 521). The comparison child is
slower and was not measured. That makes this a host-load-dependent failure
mode at about a 2 to 3 times margin. The section 6 probe should record it.

### 11. Small citation slips — note

"The stop drain at :845" (section 5): `Env.lean:845` is the counter reset
after the tail, not an emptiness test. The probe script's docstring names
sites 130/6/60, while the note (correctly) reads kinds 300/301/208/302.

### 12. The estimate — note

Two days is credible for the mirror change if finding 2's shape is
adopted and the twin traces are dropped. The note's own items, together
with the findings above, add the following. The flood environment rework
(producer loop, bounded leading run, tail consumption, per-packet contract,
`floodExact`, and its Logged copy) is the delicate part, not mechanical, and
the crypt-ring precedent (4b9dcaf, 177 lines) did not include it. The
area split touches guest, host bounds and tests (finding 7). There are at
least two probe boots with an uncertain outcome (finding 1). The campaign 1
carry is about a day (finding 6). A realistic figure is three to four days
with the traces, two without, plus carries. The order the note gives
(probe first) is right. The probe should settle time as well as memory.

### 13. A cheap extra for `e_ring_carry` — note

Decision 13.4 (no reinit at `wg_stop`) is otherwise checked by nothing
differential. A `wg_down`/`wg_up` between `e_ring_carry`'s two stages would
check it at the cost of about 0.1 to 0.2 s of the trace budget (the `wg_up`
wait). Weigh that against finding 1.

## Verdict

**Build with the named changes.** The representation is right, the C facts
the note rests on are accurate, and no arm is hidden: the trylock really is
the constant 1 on this build. Before the build, the note needs two changes:
the flood rework (finding 2) and the tail contract (finding 5) specified
exactly, and the trylock decision's sides and reason corrected (finding 4).
The fuel off-by-one (finding 3) and the frame list (finding 6) also go in.
The evidence plan of sections 6 and 7, and with it decision 13.1, is
contingent. It should go to the user only after a probe that measures the
comparison child's `since_up`, worker drain and remote comparison count on
the traces as they would be committed (findings 1, 7, 8, 10). If that probe
fails the 4.5 s bound, the capacity arms rest on the unit `#guard`s and the
strengthened tail contract, and the note should say so plainly.
