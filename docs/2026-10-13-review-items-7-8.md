# Review items 7 and 8: runner budgets versus semantics; timer operands and wrap

Design, 2026-10-13 [AGENT, fork of the coordinator]. Reconnaissance for the
simulation-target review's deferred items 7 and 8
([the review](2026-10-12-simulation-target-review.md), sections 3.6, 4.4 and
7), which the proof campaign names as R5's prerequisite for the time half of
key-lifetime enforcement ([the campaign charter](2026-10-13-charter-proof-campaign.md),
R5). Everything below was verified against `.deps/linux` 6.12.110 and measured
on the s1 oracle (identity f098cf9e) with three single-trace runs:
`d3_retransmit`, `d3_zero_key`, `b1_trie_routing`, all passing, their run
directories under the branch's `.artifacts/r78/`. Nothing is implemented here.

## 1. What the review asks and what R5 needs

- **Item 8.** `armTimer` accepts the recorded expiry when it is the requested
  delay or one less from the record's own `jiffies`, which mixes the source
  input (the caller's `jiffies` read) with a computed result (the expiry), and
  compares without wrap. `dstCacheGet` uses `>` for the C's wrap-aware
  `time_after`. Sequence numbers and times are `Nat`/`Int`. The proof needs
  expiry computed from the corresponding source read, the comparisons stated
  as the C computes them, and initial unknowns explicit.
- **Item 7.** Loop bounds that are harness patience (`4096` scheduler turns,
  `64` index draws, `256` jitter draws, `1 << 20` trie steps, ring capacity
  plus one per activation) are reported as `invariant`, i.e. as C facts. A
  legal finite C execution must not become a mirror invariant failure; a
  proof over the runner must quantify over the C's bounds, not the guest's
  waits.
- **R5** states: no encrypt or decrypt under a keypair older than
  `REJECT_AFTER_TIME` or past `REJECT_AFTER_MESSAGES`, with time from the
  recorded clock reads; after the zero-key timer, no material is used until a
  new handshake. Its time half rests on two clocks: the coarse boot clock
  (kind 208, nanoseconds) for every age test, and `jiffies` (kinds 303, 304,
  306) for the timers. R5 needs both to be the C's quantities with the C's
  comparisons, and the firing rule to rest on recorded facts.

## 2. The kernel, verified

**Two clocks, two widths.**
- `jiffies` is `unsigned long`, 64 bits on x86_64, aliased to `jiffies_64`
  (`jiffies.h:85-86`). It starts at `INITIAL_JIFFIES =
  (unsigned long)(unsigned int)(-300*HZ)` (`jiffies.h:320`) = 2^32 − 75000 =
  4294892296 at HZ 250, so the low 32 bits cross 2^32 five minutes after
  boot; the 64-bit value does not wrap for 2^64 ticks.
- `time_after(a, b)` is `(long)((b) - (a)) < 0` on `unsigned long`
  (`jiffies.h:127-130`); `time_before`, `time_after_eq` likewise
  (`:138,147-150`); `time_is_before_jiffies(a)` is `time_after(jiffies, a)`
  (`:262`). The comparison is a 64-bit signed difference.
- Every WireGuard age test is `wg_birthdate_has_expired(birthday, seconds)`
  = `(s64)(birthday + seconds * NSEC_PER_SEC) <= (s64)ktime_get_coarse_boottime_ns()`
  (`timers.h:24-29`), on `u64` nanoseconds since boot (kind 208): `send.c:25,
  66` (`REKEY_TIMEOUT` on `last_sent_handshake`), `send.c:134`
  (`REKEY_AFTER_TIME` in `keep_key_fresh`), `send.c:365` (`REJECT_AFTER_TIME`
  on the staged keypair), `receive.c:117` (one second of load), `:232`
  (`keep_key_fresh` on receive), `:253` (`REJECT_AFTER_TIME` on decrypt),
  `cookie.c:96,171`. The s64 cast makes the wrap point 2^63 ns, 292 years.
- The counter limits are `u64` compares: `REKEY_AFTER_MESSAGES = 1 << 60`,
  `REJECT_AFTER_MESSAGES = U64_MAX - COUNTER_WINDOW_SIZE - 1` with
  `COUNTER_WINDOW_SIZE = 8192 - 64 = 8128` (`messages.h:36-42`), at
  `send.c:132,381` and `receive.c:254,302-303`.
- WireGuard reads `jiffies` only to arm timers: `jiffies + delay` at
  `timers.c:62,87,149,159,185,206,216`, each through `mod_peer_timer`
  (`:30-39`) into `mod_timer`. The callback `wg_expired_retransmit_handshake`
  tests `timer_handshake_attempts > MAX_TIMER_HANDSHAKES` (`:46`, 18).
- `__mod_timer` (`timer.c:1064-1190`): a pending timer with the same
  `expires` returns at once (`long diff = timer->expires - expires; if (!diff)
  return 1`); otherwise the wheel places it by `expires - base->clk`. Not
  anchored; its own `time_after` uses are the kernel's, outside the mirror.
- `dst_cache_per_cpu_get` (`dst_cache.c:39-64`): a hit needs
  `time_after(idst->refresh_ts, READ_ONCE(dst_cache->reset_ts))` and a valid
  dst; otherwise `idst->refresh_ts = jiffies` (the miss, kind 306). The
  strict `time_after` makes a refresh in the same jiffy as the reset a miss.
- The retry loops the mirror bounds have no bound in C:
  `wg_index_hashtable_insert` (`peerlookup.c:130-152`) draws `get_random_u32`
  and `goto search_unused_slot` on a collision, unboundedly;
  `get_random_u32_below(83)` (`random.h:76-80`) rejects a `u8` draw while
  `(u8)(83 * r) < 256 % 83 = 7`, in a `for (;;)`; the worker loops
  `while ((first = ptr_ring_consume_bh(...)))` consume until empty, with
  refills possible across `cond_resched`; the trie walks are explicit-stack
  traversals bounded by the node count.

**Measured on s1** (the three runs; records decoded from `hidden.jsonl`, the
comparisons from `comparisons.jsonl` through `comparison-map.json`):

| What | Measured | Reading |
|---|---|---|
| kind 303 (arm) | 3 words `{jiffies, expires, timer address}`, e.g. `d3_retransmit` op 2: `(4294892910, 4294894216, …)`: delay 1306 = `REKEY_TIMEOUT*HZ + 56` jitter | `expires − jiffies` equals the delay in both runs seen; the one-tick slack never used here |
| kind 304 (advance) | `d3_zero_key` op 5: `4294893183 → 4295032333` (+139150) | **crosses 2^32**: the after value and the zero-key timer's `expires` (4295028033, op 3) sit above 2^32 while earlier values sit below; the mirror compares them as `Nat` and the kernel as 64-bit words, and they agree because nothing wraps at 64 bits |
| kind 306 (dst cache ts) | values 529–2213 ticks above `INITIAL_JIFFIES` | plain 64-bit `jiffies` |
| kind 208 (coarse boot ns) | 2.3 s to 560.9 s since boot (`d3_zero_key`) | the advance moves the timekeeper too, as D3 says |
| `send.c:25,66,365` | 8-byte non-constant compares `(birthday + seconds·10^9, now)`, e.g. op 3 of `d3_zero_key` at `:365`: `(0xace35d722e, 0x82fa876a2e)` | the age test records **both operands as s64**, attributed to the caller's line, never to `timers.h:28` |
| `send.c:381` | 8-byte constant compare `(0xffffffffffffe03d, 0)` | `nonce >= REJECT_AFTER_MESSAGES` compiled as `nonce > R − 1` (R = 0x…e03e): the checker's `ge` shift |
| `send.c:132` | a 1-byte compare `(0, 1)` only | the `sending_counter > 2^60` test is branchless in the built code (no 8-byte record): not declarable, a plain decision |
| `timers.c:46` | 4-byte constant compare `(0x12, 0)` | `attempts > MAX_TIMER_HANDSHAKES` with the constant 18 as written |
| `timers.c:186` | 4-byte constant compare `(6, mult)` | the jitter's `(u8)mult >= 7` as `> 6` |
| `timers.c:214` | 2-byte compare `(0, 0x19)` | the `u16 persistent_keepalive_interval` test |
| `dst_cache.c:52` | 8-byte constant compare `(0, diff)`: `(0, 0xb0)` in op 3, `(0, 0)` in op 7 of `d3_zero_key` | `time_after` is recorded as the **signed difference against 0**; op 7 is the same-jiffy miss (`diff = 0`, not after) |
| clocksource | `refined-jiffies` at start and end of every batch | tick-granular clocks, as D3 pinned |

Nothing at `receive.c:117,253` or `cookie.c` in these three traces; the
shapes are the same inlined `wg_birthdate_has_expired`, to be confirmed on a
receive trace at implementation (`d3_rx_expired_key` carries both).

## 3. What the mirror represents today

| Site | Today | The C |
|---|---|---|
| timer fields (`Types.lean:311-315`), `World.jiffiesLast`, dst-cache `refreshTs`/`resetTs` | `Nat` | `unsigned long`, 64-bit |
| `armTimer` (`State.lean:120-136`) | expiry := the record's `expires`, accepted iff `e − j ∈ {delay − 1, delay}` with `j` the record's `jiffies`; `jiffiesLast := j` | the caller computed `expires = J_c + delay` from its own read `J_c`; `mod_timer` reads `jiffies` again |
| `fireTimer`/`runTimers` (`Env.lean:362-430`) | a section accepted iff pending and `e < jHi`, `jHi := J₁ + advanceWait` after an advance, `jiffiesLast + traceBound + advanceWait` (1125 + 25 ticks) at other idle points | a timer fires at a tick with `jiffies ≥ e + 1`; the tick's `jiffies` is not recorded |
| `dstCacheGet` (`Socket.lean:152-165`) | `c.refreshTs > c.resetTs` on `Nat`, a plain `if` | `(long)(reset − refresh) < 0`, recorded as an 8-byte compare with 0 |
| `birthdateHasExpired` (`Peer.lean:165-167`) | `birthday + seconds * NSEC_PER_SEC ≤ now` on `Int` | the same on s64, recorded with both operands |
| the ten time and counter decisions (`stagedBirthdateExpired`, `decKeyExpired`, `freshExpired`, `queuedNotExpired`, `initRateLimited`, `addMacCookieFresh`, `retransmitGiveUp`, `decCounterLimit`, `stagedNonceRejected`, `freshCounter`) | outcomes only; none declares operands (`Decision.comparison` has 238 declared comparisons, only `consumeFlood` among the clock tests) | each records operands except `freshCounter` |
| `REJECT_AFTER_MESSAGES`, counters (`Send.lean:40-42`, `Types.lean:121`) | `Nat` | `u64` |
| `Activation.run` (`Batch.lean:169-190`) | `for _ in [a.iterations:bound]`, bound = `MAX_QUEUED_PACKETS + 1` (crypt, tx) or `MAX_QUEUED_INCOMING_HANDSHAKES`; exhaustion is `invariant "… did not drain"` | no bound: the loop consumes until the ring is empty, refills across yields |
| `schedule` (`Batch.lean:249`), `runSendWorkers` (`Env.lean:274`), `runTimers` (`:412`), `afterXmit` (`:802`) | `for _ in [0:4096]`; exhaustion `invariant "the scheduler loop did not converge"`, `"the send work queue did not drain"` | record-driven loops; no C bound |
| `indexInsert` (`Peer.lean:131-141`) | 64 draws, then `unsupported "64 colliding index draws"` | unbounded `goto` |
| `jitterBelowRekeyTimeout` (`Handshake.lean:353-358`) | 256 draws, then `unsupported` | unbounded `for (;;)` |
| `subtree`, `rootRemovePeerLists` (`AllowedIps.lean:231-267`) | `1 << 20` steps, then `invariant "… did not terminate"` | bounded by the node count |
| `runTimersPlaceholder` (`Env.lean:441-460`) | 64 | the domain filter's own stand-in, no C counterpart |
| `MAX_IO` (`Runner.lean:17`) | 69632 | the guest's buffer, a fixture |

## 4. Item 8: the change

**Representation.** `jiffies` values become `UInt64` wherever the mirror
holds one: the five timer fields, `World.jiffiesLast`, the dst cache's two
stamps, the arm and advance record words. Two helpers in `Leanux/Kernel/Defs.lean`
are the C macros, not approximations of them:

```lean
/-- `time_after(a, b)` (jiffies.h:127-130): `(long)(b - a) < 0`. -/
def timeAfter (a b : UInt64) : Bool := (b - a).toInt64 < 0
def timeBefore (a b : UInt64) : Bool := timeAfter b a
def timeAfterEq (a b : UInt64) : Bool := (a - b).toInt64 ≥ 0
```

The coarse boot clock and every birthday become `Int64`, and
`birthdateHasExpired` computes `birthday + seconds * NSEC_PER_SEC` in `Int64`
(wrapping as the C's s64 does) and reports both operands. Counters and nonces
become `UInt64` with `REJECT_AFTER_MESSAGES : UInt64 := 0xffffffffffffe03e`
and `REKEY_AFTER_MESSAGES := 1 <<< 60`. The point is not that a wrap is
reachable (section 4, "wrap"); it is that the mirror then performs the C's
operation, so a proof relates like to like with no side argument about
ranges.

**The arm rule, split into its two facts.** The source input is the caller's
read `J_c`; the record carries `mod_timer`'s read `J_m` and `expires`. Since
`expires = J_c + delay` exactly in the C (`timers.c:62,…`, the jitter already
drawn), `J_c := expires − delay` is the caller's read, recovered from the
record and the mirror's own delay. The semantic rule is then **expiry :=
J_c + delay**, computed by the mirror, and the record's `expires` must equal
it (publication identity: a mismatch is a wrong delay in the mirror, D3-M8's
channel, now by equality). The second fact, `J_m − J_c ∈ {0, 1}`, is an
**admissibility condition of the environment**: between the two reads only a
tick interrupt moves `jiffies` on one CPU, and the guest's waits are the
places the trace allows stalls; a larger gap is outside the fixture's timing
domain and reported as `unsupported "a stall between a timer's two jiffies
reads"`, not as a hidden mismatch. `jiffiesLast := J_m`. In the three runs
the gap was 0 at every arm.

**The firing rule.** `e < jHi` becomes `timeBefore e jHi` on `UInt64`;
`jHi` is unchanged in meaning. Whether it stays a fixture constant or becomes
a record is item 7's question (section 5, the firing window).

**Operands.** The ten decisions of section 3 declare comparisons with the
measured shapes: the seven age tests as `⟨.le, false, none, false⟩` reporting
`(birthday + seconds·10^9, now)` in `Int64`, on the caller's line (`send.c:25,
66, 134, 365`, `receive.c:117, 232, 253`, `cookie.c:96, 171`; `timers.h:28`
never owns the record); `stagedNonceRejected` and `decCounterLimit`,
`ctrRejectCounter`, `ctrRejectTheirs` as `⟨.ge, true, …⟩` (the constant is
`R − 1` in the built code, which the checker's `ge` shift absorbs);
`retransmitGiveUp` as `⟨.gt, true, …⟩` with 18; the jitter acceptance and the
persistent-keepalive interval likewise. `freshCounter` stays a plain decision:
the built code records nothing for it (measured). A new decision
`dstCacheHit` (`dst_cache.c:52`) declares `⟨.lt, true, …⟩` and reports
`((reset − refresh).toInt64, 0)`: the checker's `encode` already renders a
negative `Int` as the 64-bit two's complement the record carries.

**Wrap: what is reachable and what is not.** The 32-bit crossing is live:
`d3_zero_key`'s advance moves `jiffies` from 4294893183 to 4295032333, and the
zero-key timer's `expires` 4295028033 is compared against values on both
sides of 2^32 (`fireTimer`, `armTimer`'s delay check). Every comparison is
64-bit in the C and will be in the mirror, so the crossing is a non-event
for both, and the trace exists to prove that it stays one. The 64-bit wrap
is not reachable on this oracle: `jiffies` starts at 2^32 − 75000, an advance
moves it by at most 2^31 ticks per operation, and no trace can issue 2^33
advances. **No record can express it**: the clock record is Linux's actual
value, never steered (steering design rule: a supplied value must be a
possible output of its source, and a `jiffies_64` near 2^64 is not one this
boot can produce). The instrument that would reach it, an initial
`jiffies_64` offset at boot (the 32-bit `INITIAL_JIFFIES` trick extended to
64 bits), is a kernel behaviour change and is not proposed: the mirror's
operation being the C's operation makes the claim hold without the test.
The `ktime` clocks are likewise unreachable at 2^63 ns.

**Initial unknowns.** `jiffiesLast` is `none` until the first arm or advance
record; the three runs show the first arm within the first `wg_up`. The
firing rule before any record is the domain filter's prediction only. This
stays as is, stated: every time-dependent rule reads a recorded value or a
declared fixture constant, never a default.

**Implemented (2026-10-13, branch `task/item-8`) [AGENT, fork of the
coordinator].** As designed, with these corrections from the coverage reads
on s1, each a DWARF attribution of a multi-line condition, none a change of
meaning:
- `keep_key_fresh` (send.c:131-134): the age test is recorded at **133**,
  not 134, and the counter test `sending_counter > REKEY_AFTER_MESSAGES` is
  **recorded** as a 64-bit constant compare at **131** (`(2^60, counter)`,
  `d3_zero_key` op 3), not branchless as the table above says: `freshCounter`
  is declared `gt` against the constant.
- `decrypt_packet` (receive.c:252-254): both the age test and the counter
  limit are recorded at **252** (the `if (unlikely(` line), 102 and 94
  records over the wireguard suite.
- `counter_validate` (receive.c:302-303): both limits at **302** (196
  records); `keep_key_fresh` on receive (receive.c:230-233): the age test at
  **231** (78 records); `wg_cookie_add_mac_to_packet` (cookie.c:170-172): at
  **170** (`e_cookie_then_reinitiate`); `wg_receive_handshake_packet`'s decay
  test at 117 as designed (and a duplicate record at 118, unused).
- `timers.c:46` and `:214` as designed (25 and 16-bit records).
The arm rule's gap test is asymmetric, which the design left implicit: a
negative `J_m - J_c` (the mirror's delay too small) cannot come from a stall
and stays a hidden mismatch, so the D3-M8 sentinel keeps its channel; a gap
above 1 (a stall, or a delay too large: the record cannot tell them apart)
is `unsupported`. The sentinel patterns B1-M5 and W9-M3 follow the changed
lines. `dstCacheHit` is **not** declared: `net/core/dst_cache.c` is not an
anchored file, and anchoring it is a small stream of its own (its functions,
the `!dst` and `obsolete` tests beside the `time_after`, their witnesses);
the hit test is the C's `time_after` on `UInt64` regardless, which is the
semantic point. Measured on s1: `d3_zero_key` (the 2^32 crossing, a
non-event), `d3_retransmit` (the arm rule with jitter), `d3_rx_expired_key`,
`b1_trie_routing`, then the `wireguard` and `alloc` suites and the D3 and
steering controls.
The one-off mutant I8-M1 (the age test's left operand computed with
`NSEC_PER_SEC - 1`, so every outcome stays Linux's and only the operands
move) was rejected on `d3_zero_key` through the operand channel alone, at
all six age tests the trace exercises (send.c:25, 66, 133, 365), with no
other channel reporting; run once, then deleted.

## 5. Item 7: the budgets

Each bound, its source, and what it becomes. The rule: a C bound stays an
`invariant`; a structural bound is derived from the state it bounds; a
record-driven loop ends when the records end; a fixture bound is an explicit
environment rule whose exhaustion is `unsupported "runner budget: <name>"`,
never `invariant`.

| Bound | Source | Today | Change |
|---|---|---|---|
| `Activation.bound`: `MAX_QUEUED_PACKETS + 1`, `MAX_QUEUED_INCOMING_HANDSHAKES` | capacity plus one, called a C bound; refills across yields can exceed it in total iterations (the review's point; the ring-wrap trace consumes 1024 items in one activation and would exceed it with one refill) | `invariant "… did not drain"` | **derived**: bound := items consumed cannot exceed items enqueued; the mirror counts enqueues into the ring since the activation started (`World.enqueuedSince`), so the loop's measure is `occupancy at start + enqueues since`, exact, and exhaustion is a genuine `invariant` (consumed more than was ever produced) |
| `schedule`, `runSendWorkers`, `runTimers`, `afterXmit`: 4096 | record-driven loops; every turn consumes a record or runs a queued worker whose section consumes records | `invariant "… did not converge"` | **record-driven**: the measure is the remaining record count plus queued work; the `4096` goes; a turn that consumes nothing and queues nothing is the `invariant` (a genuine non-progress) |
| `indexInsert`: 64 draws | unbounded `goto` in C; the draws are records | `unsupported "64 colliding index draws"` | **record-driven**: loop while an index-draw record is next; exhaustion is the ordinary hidden mismatch ("no record left"), which is what a trace with 64 collisions already produces today one draw later |
| `jitterBelowRekeyTimeout`: 256 draws | unbounded `for (;;)`; the draws are records (`u8`) | `unsupported "256 rejected jitter draws"` | **record-driven**, as above |
| `subtree`, `rootRemovePeerLists`: `1 << 20` | explicit stack over a finite trie | `invariant "did not terminate"` | **structural**: fuel := the trie's node count (`nodes.size`), so the bound is the C's own (each node is pushed once); keep the `invariant` |
| the trie search's 130 steps | prefix length ≤ 128 plus the final empty iteration | fine (the review agrees) | state the source in the comment; no change |
| `runTimersPlaceholder`: 64 | the domain filter | fine | mark as the filter's, not the mirror's |
| firing window: `traceBound` 1125 + `advanceWait` 25 ticks | the guest's real-time bound and wait: **fixture** | an exact rule over fixture constants, the only time assumption the firing rule makes | two options, below |
| `MAX_IO` 69632 | the guest's buffer | explicit | no change |

**The firing window.** `jHi = jiffiesLast + traceBound + advanceWait` says a
natural firing's tick lies within the guest's real-time bound of the last
recorded `jiffies`. True of every passing run, but a bound on the harness's
patience, exactly what item 7 says a proof must not quantify over. Two ways
to make it a fact:
- *Explicit fixture assumption* (no instrument): keep the constants, name
  the rule in `Env.timing` as the fixture's timing domain, and have the
  checker fail a trace whose `timing.jsonl` real-time exceeds `traceBound`
  (today the guest fails it). R5's time half then carries the assumption
  "the firing tick is within the fixture's bound" as a stated premise.
- *A record* [recommended, tactical]: the guest reads `jiffies` at the end
  of every wait where a timer may fire (after `wg_inject`, `wg_xmit`,
  `wg_set`, `wg_up`, before `wg_observe`, and inside `wg_advance` after its
  wait), through the existing LEANUX ioctl path (`KCOV_LEANUX_JIFFIES`,
  returning `jiffies` and writing **kind 310** `{jiffies}` in the task
  stream, 8 bytes; kinds 300-309 are taken). The rule becomes exact:
  `timeBefore e J_end`, since a callback that ran did so at a tick with
  `jiffies ≥ e + 1 ≤ J_end`. Record-only, class-approved; one-off mutant: the
  guest reading `jiffies` before the wait instead of after (every natural
  firing then rejected: `hidden_mismatch`), run once and deleted. Cost: one
  ioctl case, one guest call per wait, one `Env` change; it removes the last
  fixture constant from the timer model and is what lets R5 quantify over
  recorded ticks. The `advanceWait` constant goes with it.

**What stays a runner limit, and is said so.** Chunk output size, the
16 MiB console limit, the guest's wait lengths and the 4.5 s real-time bound
remain the harness's; none of them is consulted by a mirror rule after this
change, except the firing window under the first option.

### 5.1 What was done (2026-10-13) [AGENT, fork of the coordinator]

The recommended option, with one correction to its placement. The task's
KCOV window closes at the operation's return (`harness/guest.c` captures the
task count right after the system call), before the waits; the waits' timer
sections land in the remote row, which is captured after them. So the
end-of-wait read cannot be a task-stream record: `KCOV_LEANUX_JIFFIES`
(ioctl 207, `kcov_jiffies_read`) reads `jiffies_64` and appends kind 310
`{jiffies}` (8 bytes) to the **remote** area of the process's common
handle, under that kcov's lock like `kcov_remote_stop`'s move, in one
critical section with the read, so no tick separates the value from the
record's sequence number. `kcov_choice_write` is split into an area writer
(`kcov_choice_write_area`: task, mode, area, size) and its wrapper. The
guest reads once at every wait the mirror treats as an idle point: after
`wg_inject`'s, `wg_set`'s, `wg_up`'s (the first up's early wait, before the
route adds), `wg_xmit`'s and `wg_batch`'s waits, after the wait before
`wg_observe`, and after `wg_advance`'s. The checker keys the site by its
consumer frame, `fs/ioctl.c:51`, beside the advance's, and takes the read
into the never-goes-back rule. No new site elsewhere; `kernel/kcov.c` is not
anchored; the anchored files keep their pristine line counts. Oracle pair
s2: identity `cea1e9a3…`, control `04432df8…`; patches `15f67b48…` and
`fdb1306f…`; the s1 configuration unchanged.

The mirror (`Leanux/Env.lean`): `idleTimers` and `afterAdvance` read the
operation's kind-310 value ahead (`peekSiteU64`, the record follows the
sections it bounds), run the timers with it as the window's end
(`timeBefore expires J_end`), then consume the record and carry it as the
last known `jiffies`. No record in the operation is a hidden mismatch (a
capture without the instrument); without records the domain filter's
prediction uses `Timing`'s constants, which are now the filter's and nothing
else's.

The budgets, each as the table says: `Activation.bound` (capacity plus one)
replaced by `Activation.occupancy`, the queue's items at the run's start,
with exhaustion a genuine `invariant`; `schedule`, `runSendWorkers`,
`runTimers`, `afterBatch` and `skipCutSites` record-driven
(`recordBudget`: one turn per remaining record plus one; exhaustion an
`invariant`, or `unsupported "runner budget: … (domain filter)"` without
records, `DOMAIN_FILTER_TURNS`); the index and jitter draws record-driven,
their caps of 64 and 256 gone; the two trie walks bounded by the node
count; `runTimersPlaceholder`'s loops by the pending timers and the clear
queue. `Activation.consistent` runs the same `Activation.run`, so the
elimination among suspended activations uses the derived bound too.

What the one-off mutant and the first run established is in the commits
and the integration record. Not written: `w7_refill_during_yield` (section
7): the W7 tier's measurement showed the deferred units run only after the
batch system call returns, so a refill during a yield needs a produce from
a later operation, and a suspended activation across operations is outside
the domain already; the derived bound is validated by the existing suites.

## 6. Decisions and operands, hidden inputs, environment

- Decisions: no new outcome-level decision except `dstCacheHit` (a C
  condition today modelled as a plain `if`); eleven comparison declarations
  added (section 4), each verified on s1 by a coverage read at
  implementation, as streams S and X did. Repeatable marks: none needed (one
  evaluation per call).
- Hidden inputs: none new for item 8. Kind 310 for item 7's recommended
  option, record-only, with its one-off mutant.
- Environment (`Leanux/Env.lean`, `Env/Batch.lean`): the admissibility
  condition of the arm (the stall), the firing rule on `UInt64`, the
  record-driven loop measures, the derived activation bound, and the budget
  outcomes renamed `unsupported "runner budget: …"` where a fixture bound
  remains. The mirror files change only in types and in the two macro
  helpers.

## 7. Traces

- `d3_zero_key` (exists): the 2^32 crossing on `jiffies` through an arm, an
  advance and two firings; `d3_retransmit`: the arm rule at a jittered delay;
  `d3_rx_expired_key`: the receive-side age test's operands (to measure).
- `b1_trie_routing` and `d3_zero_key` op 7 (exist): the dst-cache hit and
  the same-jiffy miss, now a declared decision with the signed difference.
- The ring-wrap trace `w7_ring_wrap` and a new `w7_refill_during_yield`
  (the W7 tier's, in `docs/2026-10-13-w7-full-ring-tier.md`): the derived
  activation bound exceeded by a refill, which today is an `invariant` and
  after the change is an ordinary run.
- No trace can exhaust the index or jitter loops (the draws are the kernel's
  random bytes, unsteered); the record-driven form needs none.
- For kind 310: every existing D3 trace, run once on the rebuilt oracle.

## 8. Risks

- A declared comparison whose built shape differs on the receive side
  (`receive.c:117,253`): measured at implementation, as the others were;
  the fallback is the plain decision, reported.
- `Int64`/`UInt64` conversions at the record boundary: the records are
  little-endian words already; the one place that must not truncate is the
  `Nat`-to-`UInt64` of the mirror's own constants (`REJECT_AFTER_MESSAGES`),
  covered by the operand check against the kernel's constant.
- The derived activation bound needs the enqueue count visible to the
  environment; the packet store with ids (review change 4, landed) makes
  every enqueue a store event, so it is a counter on `enqueuePerPeerTx` and
  the handshake-queue produce, nothing structural.
- Kind 310 needs an oracle rebuild (record-only) and lands with the next
  class-approved rebuild; until then the explicit-fixture option is the
  state of the model.

## 9. Estimate and ownership

About 0.25 WireGuard units: item 8's types and helpers 0.05, the eleven
declarations with their coverage reads 0.06, the arm rule's split 0.02, item
7's measures and derived bound 0.07, kind 310 with its ioctl, guest call,
`Env` rule and mutant 0.05. One stream for item 8 (`Leanux/Kernel/Defs.lean`,
`Decision.lean`, `Types.lean`, `State.lean`, `Peer.lean`, `Socket.lean`,
`Send.lean`, `RxData.lean`, `Timers.lean`, `Handshake.lean`), one for item 7
(`Leanux/Env.lean`, `Env/Batch.lean`, `AllowedIps.lean`'s two walks,
`Peer.lean`'s and `Handshake.lean`'s loops; and, for kind 310,
`kernel/patches/gen-choice-stream.py`, `harness/guest.c`, `harness/trace.py`,
the identity files); the claim point on the rebuilt oracle if kind 310 is
taken, else the WireGuard suites and the D3 controls.

## 10. Decisions: the user's and the tactical

**The user's: none required.** Nothing here changes the oracle's behaviour
or configuration; kind 310 is a record-only hook under the approved class,
presented with its identity at the merge. The one instrument that would make
the 64-bit wrap reachable (a boot-time `jiffies_64` offset) is a behaviour
change and is explicitly not proposed; it would be the user's case if ever
wanted.

**Tactical [AGENT], under the standing delegation:** the C's macros as the
mirror's comparison helpers rather than range arguments; the arm rule split
into publication identity and an environment admissibility condition; the
record-driven loop measures and the derived activation bound; the
record-only kind 310 over the explicit-fixture option for the firing window.
These are entered in `docs/decisions.md` with the implementation.
