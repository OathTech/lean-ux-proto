# B3 design: the timer wheel as a mirror — 2026-10-15

Status: design note for stream B3 of
[the parallel plan](2026-10-14-wireguard-parallel-plan.md), written for the
user to read before anything is built, since it moves the environment line.
Docs only, plus the probe of section 5 (`scripts/probes/b3-wheel-replay.py`,
read-only on the s4 oracle). Nothing in `Leanux/` changes with this note.
Revision 2 (this text) answers
[the independent review](2026-10-15-design-b3-review.md) at `6fe87f2`, finding
by finding, in section 14; the review was produced by a Claude Opus 5.5
reviewer, and its commit trailer names Fable at the coordinator's instruction.

## 0. In ten lines

Today the mirror holds each WireGuard timer as an expiry and learns *which*
timers fired, and in what order, from the records: each firing is a dispatch
section that names its timer, accepted if the timer is pending and its expiry
is before the end-of-wait clock read; a due timer that did not fire is never
reported. The kernel's wheel (`kernel/time/timer.c`) decides both from
arithmetic: a timer lands in a bucket whose width grows with its delay, fires
at the first tick at or after the bucket's expiry, and several due timers run
in bucket order, last enqueued first within a bucket. B3 puts that wheel into
the mirror at the thin layer, so the firing set and order become semantics
checked against the sections in both directions, with two new record-only
hidden inputs (the base clock where `__mod_timer` reads it, kind 313, and
the slot the C computed, kind 314). The tick's placement in the trace stays
the environment's. This departs from the plan's B3 row in one respect: the
kind-310 and kind-311 reads do not become derived (section 4 says why). On
the s4 oracle (section 5) the wheel, fed only the recorded clocks, predicts
every firing, every set and every order the run produced. Cost 5 to 6
agent-days to build, plus the largest proof carry in the plan.

## 1. The C, verified (Linux 6.12.110, `.deps/linux`)

### 1.1 The wheel's data (`kernel/time/timer.c`)

- Constants (`:154-188`): `LVL_CLK_SHIFT 3` (each level is 8 times coarser),
  `LVL_BITS 6` (64 slots per level), `LVL_DEPTH 9` for `HZ > 100` (`:175`),
  `WHEEL_SIZE 576` (`:188`), `LVL_START(n) = 63 << 3(n-1)` (`:165`): a delay
  below 63 ticks is level 0, below 504 level 1, below 4032 level 2, below
  32256 level 3, below 258048 level 4, and so on to level 8.
- One base per CPU: `NR_BASES 1` without `CONFIG_NO_HZ_COMMON` (`:200`;
  `# CONFIG_NO_HZ is not set`, `CONFIG_HZ_PERIODIC=y`, `CONFIG_HZ=250`,
  `# CONFIG_SMP is not set` in `kernel/config-x86_64-net-choice`). So every
  WireGuard timer lives in `timer_bases[0]` (`:268`).
- `struct timer_base` (`:251-266`): `lock`, `running_timer`, `clk` (the
  wheel's own clock, in jiffies: "updated before enqueue of a timer; during
  expiry, it is 1 offset ahead of jiffies", `:226-229`), `next_expiry` (the
  earliest pending bucket's expiry), `next_expiry_recalc`, `timers_pending`,
  `pending_map` (one bit per slot), `vectors[576]` (one `hlist` per slot).
- `struct timer_list` (`include/linux/timer_types.h:8-16`): `entry`,
  `expires`, `function`, `flags`; the slot index is stored in `flags`
  bits 22 and up (`TIMER_ARRAYSHIFT 22`, `timer.h:51-52`; `timer_get_idx`,
  `timer_set_idx`, `timer.c:552-560`). `timer_pending` is "`entry.pprev`
  not NULL" (`timer.h:145-148`): hashed in a slot.

### 1.2 Arming: `mod_timer` → `__mod_timer` (`:1240-1243`, `:1065-1190`)

- A pending timer re-armed with the same `expires` returns at once
  (`diff = timer->expires - expires; if (!diff) return 1`, `:1085-1088`).
- Otherwise the base is locked and forwarded: `__forward_timer_base`
  (`:994-1016`) leaves `clk` alone if `jiffies <= clk`; else sets
  `clk := jiffies` when `next_expiry > jiffies`, and `clk := next_expiry`
  when some bucket is already due (`:1008-1014`). **So `clk` differs from
  `jiffies` in two ways.** It *leads* by one after a pass whose last step
  was at the current tick (`base->clk++`, `:2416`; the comment at
  `:226-229`), until the next tick: an arm then sees `delta = delay − 1`.
  It *lags* when a timer of any owner is due and its softirq has not run,
  and inside a catch-up pass after an advance a callback's arm sees
  `clk = next_expiry`, the next due bucket of any owner, which can be behind
  `jiffies` by up to the advance.
- The slot: `calc_wheel_index(expires, clk)` (`:584-620`) picks the level
  from `delta = expires - clk` by the `LVL_START` thresholds (`:590-605`);
  `(long) delta < 0` is the past (`idx = clk & 63`, `bucket_expiry = clk`,
  `:606-608`); and `calc_index(expires, lvl)` (`:567-582`) rounds up:
  `e' = (expires >> 3·lvl) + 1`, `bucket_expiry = e' << 3·lvl`,
  `idx = 64·lvl + (e' & 63)` (`:579-581`). A timer therefore fires no earlier
  than `expires + 1` and no later than `expires + 8^lvl` ticks.
- Pending path: `clk = base->clk; idx = calc_wheel_index(...)`
  (`:1115-1116`); the same slot as before → only `timer->expires` is updated,
  the list position and the slot are kept (`:1123-1130`). Otherwise
  `detach_if_pending` (`:1144`), `timer->expires = expires` (`:1173`), and
  `enqueue_timer` (`:1180-1183`; through `internal_add_timer`, `:682-688`,
  if the base moved meanwhile, which it cannot on one CPU).
- `enqueue_timer` (`:655-680`): `hlist_add_head` (`:659`: last enqueued,
  first out), set the pending bit (`:660`), store the slot in `flags`
  (`:661`), `trace_timer_start(timer, bucket_expiry)` (`:663`), and lower
  `next_expiry` if this bucket expires earlier (`:670-675`).
- `detach_if_pending` (`:940-955`) clears the slot's bit when the list
  becomes empty and sets `next_expiry_recalc` (`:948-951`); `detach_timer`
  (`:928-938`) unlinks and, with `clear_pending`, nulls `pprev`.
- `del_timer` → `timer_delete` (`:1451`) → `__timer_delete(timer, false)`
  (`:1407-1432`): detach if pending, under the lock. `timer_delete_sync`
  (`wg_timers_stop`) also waits for a running callback, impossible on one
  CPU.

### 1.3 Expiry: the tick, the softirq, the pass

- `tick_periodic` (`kernel/time/tick-common.c:86-103`): `do_timer(1)`
  (`jiffies_64 += 1`), `update_wall_time`, `update_process_times`
  (`timer.c:2514-2530`) → `run_local_timers` (`:2462-2508`), which raises
  `TIMER_SOFTIRQ` iff `time_after_eq(jiffies, base->next_expiry)`
  (`:2502-2504`). The tick device is periodic (D3, section 4.5, Q1). The
  virtual advance (`leanux_time_advance`, `gen-choice-stream.py:1148-1168`)
  moves `jiffies_64` with interrupts off and raises nothing: the timers it
  makes due run at the next real tick.
- At interrupt exit, `__irq_exit_rcu` runs the pending softirqs unless the
  interrupted context was in interrupt or had bottom halves disabled
  (`kernel/softirq.c:652-666`, `:661-662`); otherwise they run at the next
  `local_bh_enable` or in ksoftirqd. `handle_softirqs` (`:536-610`) snapshots
  the pending mask (`:553`), clears it (`restart:`, `:559-560`) and runs the
  vectors in bit order (`:567-583`): `TIMER_SOFTIRQ` is bit 1 and
  `NET_RX_SOFTIRQ` bit 3 (`include/linux/interrupt.h:557-566`), so **within
  one round the timer vector runs before the NET_RX vector**; a vector raised
  during the round is served in the next round (`:596-600`) only while
  `time_before(jiffies, end)`, `!need_resched()` and rounds remain, where
  `end = jiffies + MAX_SOFTIRQ_TIME` and `MAX_SOFTIRQ_TIME =
  msecs_to_jiffies(2)` is **one jiffy at HZ 250** (`:500`;
  `jiffies.h:461-464`: `(2 + 3) / 4`); otherwise ksoftirqd takes the rest
  (`wakeup_softirqd`, `:602`). So one tick landing during a round, or a
  reschedule request (a callback waking a kworker from the idle task sets
  one), defers the remaining vectors.
- `run_timer_softirq` (`:2447-2457`) → `__run_timer_base` (`:2424-2435`:
  return if `jiffies < next_expiry`, `:2427`) → `__run_timers`
  (`:2390-2422`): **while `jiffies >= clk && jiffies >= next_expiry`**
  (`:2400-2401`): `collect_expired_timers` (`:1854-1878`) sets
  `clk := next_expiry` (`:1857`) and, level by level, moves the slot at
  `(clk & 63) + 64·i` into `heads[i]` if its bit is set (`:1865-1867`),
  stopping at the first level whose clock has nonzero low bits (`:1871`,
  `:1874`); then `clk++` (`:2416`), `timer_recalc_next_expiry` (`:2417`,
  `:1904-1970`: the earliest pending bucket, over every level), and
  `expire_timers` per collected level, **highest level first** (`:2419-2420`).
- `expire_timers` (`:1813-1852`): from the list head, `running_timer`
  (`:1828`), **`detach_timer(timer, true)`** (`:1829`: the callback sees its
  own timer not pending), unlock with irqs on (`:1845`), `call_timer_fn`
  (`:1769-1811`) → `fn(timer)` (`:1795`), where the choice-stream patch opens
  the dispatch section (D3, section 3.1). The lists in `heads[]` are live
  `hlist`s: a callback that deletes a sibling still in them unlinks it
  (`:928-938`) and it does not run; a sibling re-armed into its own slot
  keeps its position (`:1123-1130`) and does run; one moved to another slot
  is detached from the collected list (`:1144`) and does not.

So, at the first tick with `jiffies >= B`, every bucket with expiry `<= jiffies`
is run in ascending bucket expiry, levels collected at one step highest first,
each bucket last-enqueued-first. W12 Part II read the same order from the
same lines (`docs/2026-10-06-w3-w12.md`, section II.2) and was not built
because the dispatch-order records made it unnecessary (section V); B3 builds
it because the plan now wants the order as semantics.

### 1.4 WireGuard's timers (`drivers/net/wireguard/timers.c`, `peer.h:53-58`)

Five `timer_list`s per peer, flags 0 (`timer_setup(..., 0)`, `:221-228`),
armed only through `mod_peer_timer` (`:30-39`: `mod_timer` under
`rcu_read_lock_bh`, if the device is running and the peer alive) at seven
sites (`:62, :87, :149, :159, :185, :206, :216`), each `jiffies + delay`, and
deleted by `del_timer` at four sites (`:51, :170, :178, :194`) and by
`timer_delete_sync` in `wg_timers_stop` (`:235-243`). At HZ 250 and
`clk = jiffies`, the delays and their levels:

| Timer | Delay (ticks) | Level | Bucket width | Fires late by at most |
| --- | --- | --- | --- | --- |
| retransmit handshake | 1250 + [0, 83) | 2 | 64 | 256 ms |
| send keepalive | 2500 | 2 | 64 | 256 ms |
| new handshake | 3750 + [0, 83) | 2 | 64 | 256 ms |
| zero key material | 135000 | 4 | 4096 | 16.4 s |
| persistent keepalive, interval `i` s | 250·i: 250 (1 s), 500 (2 s), 750, 1250, 6250 (25 s), 7500 | 1, 1, 2, 2, 3, 3 | 8, 8, 64, 64, 512, 512 | 32 ms, 32 ms, 256 ms, 256 ms, 2 s, 2 s |

The table is the zero-lag case. No delay sits exactly one above a threshold,
so the lead of one (section 1.2) changes no level. A lag does: outside a
pass the lag is at most the softirq's latency, and the 2 s persistent
keepalive (500 ticks, four below `LVL_START(2)`) is the delay in the corpus
that a four-tick lag moves to level 2. Inside a catch-up pass after an
advance the lag can be the advance itself, and then any re-arm from a
callback can move up levels: the keepalive callback's `need_another` re-arm
(+2500, `:84-88`) and the give-up's zero-key arm (`:60-62`) are such arms,
and after a long advance the keepalive re-arm lands on level 3 or 4 (width
512 or 4096). The corpus has one such re-arm, in
`d3_keepalive_rearm_deleted`'s first advance (2600 ticks, which keeps it on
level 2); section 9 adds a trace whose advance moves it.

## 2. Today's mirror versus the C

| | Mirror today | C |
| --- | --- | --- |
| Timer datum | `Peer.timer* : Option UInt64`, `some expires` while pending (`Types.lean:309-321`); `timer_pending` is `isSome` | `timer->expires`, the slot in `flags`, membership and position in a list |
| Arming | `armTimer` (`State.lean:145-168`): consumes the caller's read J_c (kind 311) and the arm record `{J_m, expires, timer}` (kind 303), checks `expires = J_c + delay` and `J_m − J_c ∈ {0, 1}`, stores `expires`, keeps the timer's address for its section | `__mod_timer`: same-expires return, forward the base, compute the slot, keep position or re-enqueue at the head |
| Deleting | `delTimer`: the field to `none` | `detach_if_pending` |
| Which timers fire, in what order | **the records**: at an idle point, `runTimers` consumes each timer section in record order; `fireTimer` accepts it iff the named timer is pending and `time_before(expires, J_end)` (`Env.lean:364-397`); a due timer with no section is not an error (the trace's `expect` label catches it) | the pass of section 1.3: every bucket with expiry `<= jiffies`, in bucket order |
| The window | the end-of-wait read J_end (kind 310, review item 7) bounds the firings | the softirq's `jiffies` at each pass |
| Several same-kind timers in one pass | the order the records show (W12 results, dispatch-order) | ascending bucket expiry, level, last enqueued first |
| A timer whose `expires < J_end` but bucket expiry `> J_end` | fires or not, "benign, the mirror follows the sections" (`d3_between_zone`, D3 section 17.3) | does not fire |
| Domain filter (no records) | `runTimersPlaceholder`: earliest `expires` first | n/a |

The mirror's rule is sound in one direction (a section is accepted only for a
timer that could be due) and silent in the other (a due timer that did not
fire is not reported by the mirror). The order is an input, not a prediction.

## 3. The change at the thin layer

### 3.1 State: the wheel's per-timer data, and the base restricted to the armed set

The C keeps per timer `expires` and the slot (`flags`), and per base the
slot lists, whose order is the enqueue order, and `clk`. The mirror keeps
the same information; two layouts are possible and the choice bears on the
proof carry (section 10):

- **Per-timer (recommended).** Each of the five timers of a peer carries,
  beside today's `expires : Option UInt64` (unchanged in type), three new
  fields: `slot : Nat` (the C's `flags` index), `bucketExpiry : UInt64`
  (the slot's next visit, set at enqueue: section 1.2) and `enqueued : Nat`
  (a stamp from a `Kernel.timerEnqueues` counter, the list position:
  within a slot the C's list is the timers of that slot by stamp
  descending). `Kernel.timerClk : UInt64` is the last recorded base clock
  (section 3.2). The slot lists are a derived view, computed by the pass as
  "pending timers with this slot, by stamp descending". `Kernel` gains two
  scalars and `Peer` three fields per timer, all additive, so the full-`Kernel`
  frames and `WGKernelView` keep their fields. W12's unbuilt design had this
  shape (`docs/2026-10-06-w3-w12.md`, II.5).
- **Per-base.** `Kernel.timerBase : TimerBase` with `vectors : Array (List
  TimerRef)` of 576 slots head first and `slot : HashMap TimerRef Nat`, the
  C's `vectors` and `flags` literally; `expires` stays with the peer. The
  shape is the C's, and it adds a field to `Kernel`, which moves
  `WGKernelView` and every frame naming `Kernel`'s fields (section 10).

Both carry the same information and the same invariants; the proofs relate
them by a bijection either way. I recommend the per-timer layout for the
carry; the user may prefer the per-base shape for the thin-layer rule's
"same shape", which is U5 in section 13.

**Invariants, checked at run time** (`invariant`, fail-noisy, not only in
unit tests): a timer is pending (`expires.isSome`) iff it has a slot;
`bucketExpiry` is in `(expires, expires + 8^level]` at enqueue; no two
pending timers share a stamp; and at `retirePeerUnits` (a released peer,
`Defs.lean:1508-1516`; peer ids restart on a fresh device) the released
peer's timers are not pending, else the invariant fails.

**Why the bucket expiry is stored, not recomputed.** On the same-slot path the
C keeps the timer where it is (`:1123-1130`); the slot's next visit is the
bucket expiry computed when it was enqueued, whatever the new `expires`
says, and recomputing from the new `expires` would be wrong when the new
index aliases one wrap later (an overdue timer re-armed into its own slot
fires at the current step, not a wrap later). `pending_map` is "some pending
timer has this slot" and `next_expiry` is not represented; section 3.3 says
why that is exact for the subset.

### 3.2 Arming: `modTimer` as `__mod_timer`, with the clock recorded where the C reads it

`armTimer pid t delay jc?` keeps its signature and its two checks, then runs
the C's paths:

1. `expires := J_c + delay` (as today, checked against the arm record).
2. If pending with the same `expires`: return (`:1085-1088`); nothing else
   changes and no further record is consumed.
3. Otherwise the C locks and forwards the base. The base clock after the
   forward is the **kind-313 record** `{clk, timer}`, written for an armed
   function on both paths right after `forward_timer_base` (`:1107` on the
   pending path, `:1141` on the not-pending one; `:1167` is the cross-base
   path, unreachable on one CPU), consumed here and checked, fail-closed:
   `time_before_eq(clk, J_m + 1)` (the lead of one at most); `clk` never
   behind the previous recorded `clk` (`__forward_timer_base` never rewinds);
   if a modeled bucket `B <= J_m` is pending, `clk <= B` (the forward stops
   at the earliest due bucket, `:1008-1014`); if the arm is inside a pass
   whose current step is `B`, `clk >= B + 1` (`:2416`). A violation is a
   hidden mismatch. The record names the timer; it must be the one the arm
   record named.
4. `(idx, bucketExpiry) := calcWheelIndex expires clk` (`:584-620`,
   `:567-582`), on `UInt64` with the C's `time_before`.
5. If pending and `idx` equals the timer's slot: update `expires`, keep the
   slot, the stored bucket expiry and the stamp (`:1123-1130`). **This
   decision is computed from the mirror's state, never read off a record.**
6. Else detach if pending (`:1144`), set `expires` (`:1173`), set the slot,
   the bucket expiry and a fresh stamp (`:659-661`), and consume the
   **kind-314 record** `{idx, bucket_expiry, timer}` from `enqueue_timer`,
   whose values must equal the mirror's (a difference is a wrong wheel
   arithmetic in the mirror: a hidden mismatch, the channel of mutants
   B3-M1, B3-M2 and B3-M7). A kind-314 record where step 5 decided "same
   slot", or none where step 6 decided "move", is a hidden mismatch: the
   record checks the decision, it does not make it.

Why a second site rather than a fail-closed rule without one: the
alternative is to let `clk` range over its admissible interval and report
`unsupported` whenever the same-slot decision depends on where in it `clk`
falls. Outside a pass that interval is `{J_m, J_m + 1}` and the decision
rarely depends on it; inside a catch-up pass the lag is up to the advance
(section 1.2) and the interval spans levels, so every re-arm from a callback
after a long advance would stop the trace. Two record-only hooks are cheaper
than a rule that fails the traces B3 is for.

`delTimer` becomes `detach_if_pending`: clear the slot, the bucket expiry
and the expiry. `peerRemoveAfterDead`'s `wg_timers_stop` deletes the five as
today.

### 3.3 The pass: `__run_timers` at a step, re-scanning after every callback

A pass at the jiffies value `J` (the C's `:2390-2422`, over the modeled
subset): while some pending modeled timer has `bucketExpiry <= J`, take the
smallest bucket expiry `B` (the C's `next_expiry` step); of the pending
timers at `B`, the highest level first (`:2419-2420`), and within a slot the
newest stamp first (`:659`); detach that timer (`:1829`); then
`call_timer_fn` is the section: the next record must start that callback's
section and name this timer (its address from the arm record, as
`fireTimer` resolves today); then the callback (`WG.timerCallback`,
unchanged). **After each callback the wheel is scanned afresh**, not a
snapshot of the collected bucket: a sibling the callback deleted is gone and
does not run (`wg_expired_retransmit_handshake`'s give-up deletes the
keepalive, `timers.c:51`, which can share its level-2 bucket); a sibling it
re-armed into its own slot keeps its stored bucket expiry and runs; one it
moved has a later bucket and does not. These are the three outcomes of
section 1.3's last bullet.

Why `next_expiry` over the full wheel is not needed: the C's loop steps
`clk` through every pending bucket expiry `<= jiffies` in ascending order,
whatever its owner, so a modeled bucket with expiry `B <= jiffies` is
collected at the step `clk = B` of the first pass whose `jiffies >= B`
(section 1.3). Unmodeled timers change which steps exist, not whether or
when a modeled bucket is run. They do change `base->clk` at an arm, which
is why `clk` is recorded.

A callback's re-arm during a pass is `expires = jiffies + delay > jiffies`,
never due in the same pass (D3 section 2.3, item 3); its slot is computed
with the recorded `clk` of that arm, inside the pass.

### 3.4 The firing rule at idle points: passes bounded by the stream

`idleTimers` and `afterAdvance` keep their place (the guest's waits after
`wg_set`, `wg_up`, `wg_inject`, `wg_xmit`, `wg_batch`, before `wg_observe`,
and after `wg_advance`, `Syscalls.lean:383-391`) and their kind-310 read
`J_end`. A wait can contain several ticks, each running its own pass, with
the work the callbacks queued (the send worker, the crypt workers, the
loopback NET_RX) running between passes and possibly arming or deleting
timers; today's `runTimers` (`Env.lean:406-442`) accepts such a stream
(`T W N T W N`). The rule is therefore stated over passes whose boundaries
the section stream places:

> **E1.** At an idle point whose read is `J_end` (with the bound `J_pass`
> of the last paragraph below):
> 1. the next timer section is always the earliest pending modeled bucket
>    (level descending, newest stamp first), at a bucket expiry `<= J_pass`;
> 2. a non-timer record may follow a timer section at step `B` only when no
>    other pending modeled timer has bucket expiry `B` (a step is never
>    split; the work between passes runs in record order and may arm or
>    delete, as the C's workers do);
> 3. at the read, no pending modeled timer has bucket expiry `<= J_pass`;
> 4. no section runs a timer whose bucket expiry is `> J_pass`.

Items 1 and 4 are the direction today's rule has, sharpened from `expires`
to the bucket expiry (`d3_between_zone` becomes a rule, not a 3 % lottery);
item 3 is the direction it lacks. The only freedom left to the environment
is the unrecorded tick `J_i ∈ [B_i, B_{i+1})` of each pass, which places the
work between passes. The stream `T(B1) W N T(B2) W N` of two buckets due at
different ticks of one wait is accepted: `T(B1)` is the earliest bucket;
the boundary `W` is allowed since no other timer has bucket `B1`; the work
runs; `T(B2)` is then the earliest pending bucket, whatever the work armed
or deleted; at the read nothing `<= J_end` remains. A unit test covers this
stream, and section 9 names a trace for it.

**The bound `J_pass`.** For a wait after any operation but an advance,
`J_pass = J_end`: a tick between the last pass and the read would have run
another pass before the task resumed (`__irq_exit_rcu`, `:661-662`: the
guest is in task context with bottom halves enabled during its wait and its
read), with the one exception E2 below. For `wg_advance`, the jump raises
nothing (section 1.3); a pass over what the jump made due has run only if a
tick followed it, that is `J_end > after` (D3 section 13: the first arm
after an advance sees `after + 1`, which `jiffies_problems` already checks).
With `J_end = after` nothing made due by the jump has fired, `J_pass =
before`, and the sections land in the next operation as today.

> **E2.** A pending modeled timer with bucket expiry `<= J_pass` and no
> section before the read is either the kernel deferring the timer softirq
> to ksoftirqd past the read, or a mirror mistake (a bucket predicted too
> early, a deletion the mirror missed). The mirror tells them apart by
> looking ahead in the trace's records: if that timer's section appears
> later in the stream (after the read in this operation's remainder, or in
> a later operation), the outcome is `unsupported "a due timer's softirq
> deferred past the end-of-wait read"`, outside the fixture's timing domain
> like the two-read gap above one tick (review item 8); if it never appears,
> the outcome is a hidden mismatch, "a due timer did not fire". The trigger
> of the deferral is section 1.3's: one tick landing during a softirq round
> (`MAX_SOFTIRQ_TIME` is one jiffy here), a reschedule request, or ten
> rounds.

The runner holds the trace's remaining records per operation, so the
lookahead is a scan, not a new instrument. With it, no mirror mistake can
pass as a host-timing outcome in the direction E1 adds, which is the
condition of U4.

The tick's **placement** in the trace is otherwise unchanged and stays the
environment's: a timer section at a non-idle point (inside a worker's body or
a syscall) remains a hidden mismatch (D3 section 5.3), since the mirror cannot
run a callback mid-body; the section's position in the stream is the only
record of where the tick landed, and no new record is proposed for it.

### 3.5 The timer softirq relative to NET_RX

What determines it (section 1.3): the tick raises `TIMER_SOFTIRQ`; NET_RX is
raised by the data path (a loopback transmit from a worker, an injected
datagram). In one `handle_softirqs` round the timer vector runs first; a
tick that lands inside a NET_RX section raises the timer vector for the next
round, after the NET_RX action returns, or for ksoftirqd (E2). At an idle
point no NET_RX work is pending when the tick fires (the operation's own
waits drained it), and the NET_RX sections that follow a timer pass come from
the work its callbacks queued (a keepalive's encrypt and transmit workers,
whose loopback send raises NET_RX at the worker's `local_bh_enable`), so
they follow the worker sections in the stream. The mirror already runs that
tail in record order. **No new record and no new rule**: the relative
placement is forced by the data flow at idle points, and a tick inside a
NET_RX section is the mid-body case of section 3.4. Section 5 measured the
observed pattern.

### 3.6 The domain filter

`runTimersPlaceholder` (no records) runs the pass with `clk = the last known
jiffies` at every arm and the fixture's window (`Timing`), so its prediction
is the wheel's order rather than earliest-expiry-first.

## 4. Records: what stays, what is checked, what is new

| Record | Today | After B3 |
| --- | --- | --- |
| kind 311, the caller's `jiffies` read | hidden input | **stays**: the clock WireGuard reads, the source input of the expiry. Deriving it from the arm record would be the "publication identity" the pre-release review withdrew (finding 2) |
| kind 303, `{J_m, expires, timer}` at `mod_timer` | hidden input; expiry check; the timer's identity | **stays**: the expiry check (D3-M8's channel) and the identity |
| kind 304, the advance | hidden input | **stays**: the operation's effect on `jiffies_64` |
| kind 310, the end-of-wait read | the window's end for `expires < J_end`, accept-only | **stays, consumer changed**: `J_pass` for E1, both directions. It cannot be derived: how many ticks a wait took is a clock, and the fired set alone would only bound it (accepting any downward-closed set is the fail-open rule B3 removes) |
| kind 300/301, the sections | the firing choice: which timer, in what order | **checked, not chosen**: the section must be the pass's next timer; the callback's records still live inside it |
| **kind 313 (new)**, `{base->clk, timer}` in `__mod_timer` after `forward_timer_base`, both paths | — | the base clock at the arm, a hidden input (it depends on timers outside the modeled set); read where the C reads it, so the same-slot decision is computed |
| **kind 314 (new)**, `{idx, bucket_expiry, timer}` in `enqueue_timer` | — | the C's slot and bucket expiry, which check the mirror's arithmetic and its same-slot-or-move decision |

The plan's B3 row said the kind-310/311 reads "become derived". They do
not, for the reasons in the table; what becomes semantics is the firing set
and the order, which were records, and what becomes checked is the
dispatch choice the sections carried. The user deciding U1 should weigh B3
on that, not on the plan's wording.

The environment line after B3: the mirror owns the wheel's per-timer data,
the arm paths, the pass and its order, and both directions of the firing
rule; the environment owns the tick's placement (the section's position,
idle points only, the pass boundaries of E1), the number of ticks a wait
took (kind 310), the base clock (kind 313), and the deferral (E2).

## 5. Measurement on s4

**Method.** The probe is committed as `scripts/probes/b3-wheel-replay.py`
(stdlib Python plus `addr2line`); it takes a check run's output directory
and the kernel build directory. The run: the `wireguard` suite on the s4
oracle (identity `6b2018b9…`) from this worktree with `--out` into its
private `.artifacts`, deleted after the probe (ephemeral; the command and
the probe reproduce it). The probe replays each trace's coverage-child
records in sequence order and feeds the wheel arithmetic of section 1.2 with
only the recorded clocks: at each kind-303 record it places the timer with
`clk = J_m` (the no-lag case, since kind 313 does not exist yet), applying
the same-expires, same-slot and re-enqueue paths; each timer section is
judged at the moment it starts against the earliest pending bucket at or
before the operation's kind-310 read; and at every read, each pending timer
with bucket expiry at or before the read that has no section is reported by
disposition, never absorbed. Deletions are not recorded; the probe performs
the ones the mirror's control flow performs from the records that mark that
control flow exactly, each at its C site (the probe's header lists them: the
handshake completion at `timers.c:194` through the kind-205 read at
`timers.c:197` from `receive.c:179`/`:347`; the keepalive deletion at
`timers.c:170` through the kind-311 read that follows an initiation or
response send and through every transmit worker section; the new-handshake
deletion at `timers.c:178` through the same handshake markers and the
kind-208 age test at `receive.c:253` of each received data packet; the
give-up's deletion at `timers.c:51` through the zero-key arm inside the
retransmit section; `wg_timers_stop` through the `wg_down`, `wg_delete` and
`wg_netns_close` operations). A clock-record marker is attributed to a peer
only when one peer can be meant; otherwise the timer stays pending and can
only produce an "unexplained" report. Two stand-ins remain, named in the
probe: a data packet the counter rejects after the age test, and a peer
removed by `wg_set`, both of which could only add unexplained reports.

**Run.** 261 traces of the `wireguard` suite (the corpus and 200 generated),
status pass on s4, 2026-10-15, from this worktree
(`LEANUX_KERNEL_DIR=<main>/.artifacts/kernel-net-choice-s4 capped --
scripts/in-bundle python3 -m evaluator.check --suite wireguard --no-build
--out .artifacts/check/b3-measure2`, then `python3 -I
scripts/probes/b3-wheel-replay.py .artifacts/check/b3-measure2
<main>/.artifacts/kernel-net-choice-s4`); 156 traces arm a timer. (Revision 1
reported a previous run of the same suite through a weaker replay; the
figures below are this run's, from the committed probe.)

| Measured | Count |
| --- | --- |
| Arm records (kind 303) | 848 |
| of which a pending timer re-armed with the same `expires` (`__mod_timer:1085-1088`, nothing changes) | 94 |
| of which a pending timer re-armed into its own slot (`:1123-1130`, position and bucket expiry kept) | 166 |
| of which a pending timer moved to another slot (`:1144`, `:1181`, re-enqueued at the head) | 86 |
| Fresh or moved placements by level: 1 / 2 / 3 / 4 | 3 / 304 / 164 / 117 |
| End-of-wait reads (kind 310), i.e. idle points | 1312 |
| Advances (kind 304) | 44 |
| Timer sections (firings) | 46, in 40 operations |
| Operations with several firings in one pass | 5 |
| **Firings the wheel predicts as the next to run (set and order)** | **46 of 46** |
| Operations whose firings the wheel predicts exactly | 40 of 40 |
| Timers predicted due at a read with no section, by disposition | **0** in every disposition: 0 fired later (the deferral, E2), 0 unexplained |
| Deletions the probe performed at the C's sites | 118: handshake complete at `timers.c:194` (via `receive.c:179`) 94; an initiation sent (`send.c:37`) 1; the transmit worker ran (`send.c:248`) 9; `wg_timers_stop` at `wg_down` 9 and at `wg_delete` 5 |
| Deletion markers left ambiguous (several peers; timers kept pending) | 0 |
| Timers with `expires < J_end` and `bucket_expiry > J_end` (the between zone) | 2, both `d3_between_zone`'s zero-key timer at two reads, correctly not fired |
| Arms while a modeled timer was overdue (the `clk` lag the records can see) | 0 |
| Operations with both timer and NET_RX sections | 32, in every one the timer sections precede the NET_RX ones |

The five multi-firing passes are `w12_retransmit_lifo` (two retransmits, the
later-enqueued first), `w12_three_retransmit` (three, last-enqueued-first),
`d3_zero_key` and `l_delete_after_clear_work` (the persistent keepalive's
level-3 bucket, then the zero-key timer's level-4 bucket, ascending bucket
expiry) and `d3_zero_key_after_new_handshake` (the new-handshake timer, then
the zero-key timer). Their section patterns are timer sections first, then
the workers the callbacks queued, then the NET_RX sections their loopback
sends raise (`TTW`, `TTWNW`, `TTWNWN`, `TTTWNWNWN`), as section 3.5 says. No
operation in the run has two passes separated by work (the `T W N T` stream
of section 3.4), so E1's item 2 is untested by this corpus and is covered by
the unit test and the trace of section 9. The keepalive re-arm of
`d3_keepalive_rearm_deleted` is among the nine the transmit worker deleted
(`send.c:248`), which is what the D3 control was built to show.

**Verdict.** On this oracle, the wheel's arithmetic fed only the recorded
clocks (`clk = J_m`, the no-lag case) and the deletions the C's control flow
performs predicts every observed firing, every fired set at every idle
point and every order, including all five multi-timer passes and the
between zone, and leaves no due timer unaccounted for: both directions of
E1 hold on 1312 idle points, with no deferral past a read. What the records
cannot show is the `clk` lag from timers outside the modeled set (section
1.2): none of the 848 arms needed one to match, so on this corpus the lag
changed no level, and the one re-arm inside a catch-up pass
(`d3_keepalive_rearm_deleted`, advance 2600) stays on level 2 at any lag
that advance allows; kind 313 makes the lag recorded rather than assumed,
and the trace of section 9 makes it visible. The stop risk of section 11 did
not materialise.

## 6. Effects

- **Key lifetime over the wheel (campaign 3, lane E).** What B3 buys is the
  must-fire direction. Today the mirror accepts a run in which a due timer
  did not fire, so no statement about when the zero-key callback runs can
  be made over the mirror. Under E1, in every run the mirror accepts (E2
  and mid-body ticks excluded), a zero-key timer armed at `J_c` with
  `expires = J_c + 135000` and the recorded `clk` has run its callback, and
  queued the clear work, by the first idle read with `J_end >=` its bucket
  expiry, which is at most `expires + 8^lvl` with `lvl` computed from the
  recorded clock: level 4 (width 4096) at zero lag, higher inside a long
  catch-up pass (level 5, width 32768, is reachable there). That is the
  statement campaign 3 can pose over the mirror ("key lifetime over the
  timer wheel" in the plan), conditional on the liveness premise that
  `jiffies` reaches the bucket expiry at an idle point.
- **The D3 corpus** (`d3_*`, `w12_*`, `tc_advance_wait0`, the keepalive
  traces): no trace changes. Every pass is now checked both ways; the
  `expect: fired:` labels become redundant with the rule but stay as the
  trace's intent. `d3_between_zone` turns exact. `w12_retransmit_lifo` and
  `w12_three_retransmit` check the order against the sections instead of
  taking it from them. The generator's `fire_advance`/`quiet_limit`
  margins (`evaluator/generate.py:1425-1447`) stay as heuristics; they could
  later ask the mirror's wheel for the exact advance, which is not part of B3.
- **The timer control** `tc_advance_wait0` (guest variant `advance-wait-0`:
  no absorbing poll, no wait, the read right after the ioctl) keeps its
  stated outcome under section 3.4's advance rule. Normally `J_end = after`:
  `J_pass = before`, E1 demands nothing, the keepalive's section lands in the
  following `wg_get`, a non-idle operation, hence a hidden mismatch, as
  today. If a tick happens to land between the ioctl's return and the read,
  the pass's sections sit in the advance operation and are accepted, and the
  work the callback queued runs during `wg_get`, whose records then
  mismatch. Both are in the control's accepted set
  (`{'hidden_mismatch', 'dispatch sections opened but not recorded'}`,
  `scripts/wg-d3-controls.py`).
- **The checker**: `jiffies_problems` (`evaluator/check.py:679-750`) gains
  kinds 313 (16 bytes) and 314 (24 bytes): each names the timer of the
  kind-303 record it follows (the site guard "resolved by kind" would
  otherwise lose); `clk` never goes back and `clk <= J_m + 1`. Two new sites,
  `HiddenSite.timerClk` and `.timerEnqueue` (kind class `wheel`, resolved by
  kind like 304 and 310, since the hooks have no caller frame of ours).
  `kernel/time/timer.c` stays unanchored (section 8).

## 7. Oracle changes

Two hooks, both record-only under the approved class, both for a function in
the armed set with the same lock-free membership test as `kcov_timer_arm`
(`gen-choice-stream.py:798-827`):

- kind 313 `{base->clk, timer}` (16 bytes) in `__mod_timer` right after
  `forward_timer_base` on the pending path (`timer.c:1107`) and the
  not-pending path (`:1141`); the cross-base path (`:1167`) is unreachable
  with one CPU and gets no hook;
- kind 314 `{idx, bucket_expiry, timer}` (24 bytes) in `enqueue_timer`
  (`:655-680`), beside `trace_timer_start`.

As built (section 15.1): `__mod_timer` is out of line in this build, so its
`_RET_IP_` is inside `timer.c`; it takes its caller's return address as a
parameter, which its six callers pass as `_RET_IP_`, and both records
resolve to the arming line (`timers.c:37`) like the arm record. The kind-314
record is written at `__mod_timer`'s enqueue statement (`:1180-1183`, after
`enqueue_timer` or `internal_add_timer`, which now returns the bucket
expiry) from the slot stored in the timer's flags and that bucket expiry:
the values are `enqueue_timer`'s own, and the same-slot path writes none.

Both run under `base->lock` with interrupts off. They are written with the
mode check and `kcov_choice_write` directly, **without the steering lookup**,
exactly as the kind-304 writer does (`gen-choice-stream.py:983-1003`:
`check_kcov_mode` at `:995-997`, `kcov_choice_write(t, 304, …)` at `:1000`,
inside `local_irq_save`); nothing should steer these values. (Revision 1
said the kind-304 writer took the steering lock under the timekeeper locks;
it does not, and `kcov_choice_ip`'s path through `kcov_steer_apply` would
take `kcov_remote_lock` and `steer->lock` under `base->lock`, an order the
build would otherwise have to justify.) No configuration or behaviour
change; no new boot parameter. The identity and patch hash land with the
batch's rebuild, as the rule says.

Flagged for the user in U2: these are the first records written from inside
the wheel's locked region, at two sites. The lock-free alternative (one
record in `mod_timer` after `__mod_timer` returns, `{ret, timer->expires,
timer_get_idx(timer)}`) loses `base->clk`, so the same-slot decision could
not be computed before the record, which is finding 1 of the review; it is
not recommended.

## 8. Decisions and operands

The wheel's comparisons (`calc_wheel_index`'s nine thresholds, the
same-expires and same-slot tests, the pass's `time_after_eq` loop) are in
`kernel/time/timer.c`, which is not an anchored file (`correspondence/
kcov.json` anchors `drivers/net/wireguard/*` and the FS files), so they get no
KCOV witness and no comparison record, and the mirror implements them as
plain Lean on `UInt64` with the C's `time_before` family, **not as declared
`Decision`s**. The check of the arithmetic is the kind-314 record: `idx` and
`bucket_expiry` are the C's computed results, compared for equality at every
enqueue, which is a stronger check than a branch witness; the two early exits
(same expires, same slot) are witnessed by the absence of a kind-314 record
against the mirror's computed decision, and they have the same effect, so
the difference between them is unobservable. The boundary is to be declared
in `correspondence/kcov.json`'s notes and `docs/proofs.md`: `kernel/time/
timer.c` is **mirrored but unanchored**. The existing hooks in `timer.c` add
lines (`gen-choice-stream.py:1172-1201`), which is fine while the file is
unanchored and would not be if it were anchored; U3's choice is coupled to
that. WireGuard's own timer decisions (`timers.c:46, :60, :84, :110, :112,
:140, :147, :156-157, :214`) are unchanged.

## 9. One-off mutants and traces (each mutant run once in the build's commit, then deleted)

- **B3-M1**, rounding down: `calc_index` without the `+ 1`. Rejected by the
  kind-314 `bucket_expiry` on the first arm of every D3 trace.
- **B3-M2**, a level threshold off: `LVL_START(4)` as 135001, which moves
  the zero-key timer (135000) to level 3 (slot `192 + …` instead of
  `256 + …`, width 512 instead of 4096). Rejected by the kind-314 `idx` at
  the zero-key arm of every session trace. (Revision 1's `LVL_START(2)` as
  512 moved only delays in `[504, 512)`, which no WireGuard delay has.)
- **B3-M3**, FIFO within a bucket (push at the tail): rejected by
  `w12_retransmit_lifo` (the section names B, the mirror's pass predicts A).
- **B3-M4**, the must-fire direction dropped (a due timer without a section
  accepted): no live trace changes verdict, so this one is an evaluator
  control on a replay capture with a timer section removed, like the
  allocation evaluator controls; rejected by the E1 report.
- **B3-M5**, position never kept (always re-enqueue): rejected by a kind-314
  record the mirror expects and the kernel did not write, on the persistent
  keepalive's traversal re-arms within one bucket (`c_keepalive_endpoint`,
  `d3_persistent_keepalive`).
- **B3-M6**, the between zone fires (`expires <= J_end` as the due test):
  rejected by `d3_between_zone` when its phase puts the bucket boundary past
  the read (about 97 % of runs; an inconclusive verdict otherwise, reported
  as such like Q-M1).
- **B3-M7**, the clock channel ignored (`clk := J_m` instead of the kind-313
  value): rejected by the new trace `d3_keepalive_rearm_catchup` below,
  where the kernel's `idx` (level 3) differs from the mirror's at `J_m`
  (level 2).

Traces to add (`scripts/wg-d3-corpus.py`):
- `d3_keepalive_rearm_catchup`: a session, two injected data messages without
  a send between (`need_another_keepalive` set, as `d3_keepalive_rearm_deleted`),
  then one advance of 4200 ticks: the keepalive fires in the catch-up pass
  and its callback re-arms at `jiffies + 2500` with `clk` at the next due
  bucket of any owner, about 1700 ticks behind, so `delta ≈ 4200` and the
  re-arm lands on level 3; the transmit worker deletes it, so only the
  kind-313/314 records show it. The arm records are its evidence and
  B3-M7's channel.
- a two-pass wait: a 1 s persistent keepalive (250 ticks, level 1) and a
  second timer whose buckets fall less than one wait apart, for instance
  two injects then an advance whose 25-tick absorbing wait reaches the
  second bucket; the generator's `steered_timers` can place it. It
  exercises E1's items 1 and 2 across a `T W N T` stream.
- The order "highest level first at one step" has no witness: it shows only
  when buckets of two levels have the same expiry `B` (a multiple of `8^l`
  for the higher level), which the generator cannot force since it does not
  choose `jiffies`; a unit test of the pass covers it, and the note records
  that the live corpus does not.

A sentinel is kept only if one of these replaces an existing channel; B3-M1
would replace nothing and stays one-off.

The results of the build's runs are in section 15.

## 10. Proof-tree frames touched (read-only, `git show`)

Campaign 1 (`proofs/campaign`, 25 files, 588 theorems in them): every file
that names `armTimer`, `fireTimer`, `runTimers`, `runTimersPlaceholder`,
`idleTimers`, `afterAdvance`, `runTimerSection` or `timerCallback`. The
heaviest restate the mirror's code verbatim and are rewritten against the
pass, not re-proved: `WG/Environment/TimerSource.lean` (11 references; a
literal copy of `fireTimer` closed by `rfl`), `WG/Lifetimes/EnvTimersAudit.lean`
(82; audit copies of `runTimers`, `fireTimer`, `idleTimers` and
`afterAdvance` with erasure and preservation theorems), `Logged/Operations.lean`
(39), `WG/Lifetimes/EnvDeferredCalls.lean` (18), `WG/Keypairs/Frames/Env.lean`
(18), `WG/Keypairs/Evolution/Operations.lean` (18),
`WG/Lifetimes/MaintenanceTimers.lean` (12), `WG/Lifetimes/SyscallsAudit.lean`
(10), `WG/Lifetimes/TimerCallbacks.lean` (9), `Logged/Syscalls.lean` (8),
`Logged/Advance.lean` (7), `Logged/TimerPass.lean` (3),
`WG/KeyLifetime/Statements.lean` (1). With the per-base layout, `Kernel`
gains a field and `Framing/WGKernel.lean`'s `WGKernelView` (referenced by 54
files on `proofs/campaign`) and every frame naming `Kernel`'s fields move
too; with the per-timer layout (section 3.1) `Kernel` gains two scalars and
`Peer` additive fields, which localises the carry to the files above. The
carry is **two to four agent-days**, the largest in the plan; the campaign's
lag-and-repair rule applies.

Campaign 2 (`proofs/campaign-2`, 6 files): `Logged/Operations.lean`,
`Logged/Syscalls.lean`, `WG/Keypairs/Evolution/Operations.lean`,
`WG/Keypairs/Frames/{Env,WGBase,WGTransitions}.lean` — all shared layers
campaign 1 owns, so campaign 2 carries by merge. H6 (timer discipline) has no
files yet and "deliberately does not depend on" the wheel; its claims are
about arming sites and delays, which `armTimer` keeps (same signature, the
same two checks, two more records consumed), so H6 re-proves `armTimer`'s
body lemmas and nothing in its statements.

## 11. Risks, the stopping one first

1. **Stop risk: the wheel does not predict the s4 oracle.** If section 5
   showed firings the wheel fed with the recorded clocks does not predict
   (sections for timers whose bucket is not due, or an order not the
   wheel's) beyond what the no-lag approximation of `clk` explains, the pass
   would not be a function of the recorded inputs and the lane would stop at
   this note; lane E's key lifetime would stay record-based, as the plan
   allows. **Measured: it did not happen** (section 5), so the stream can
   proceed.
2. **The deferral case (E2) is frequent under host load.** One tick landing
   during a busy softirq round defers the timer vector at HZ 250, so the
   rate is load-dependent; traces then stop as `unsupported` at a rate the
   contended-host rule may not allow. Today such a firing lands in the next
   operation, which is already a hidden mismatch unless that operation is an
   idle point, so the rate is bounded by today's pass rate; section 5 counts
   late firings directly.
3. **The carry on campaign 1** (section 10): two to four agent-days, the
   largest in the plan; mitigated by the per-timer layout, `Peer.timer*`'s
   types and `armTimer`'s signature.
4. **The lag inside catch-up passes** (section 1.2): with `clk` recorded it
   is harmless to correctness, but a re-arm from a callback after a long
   advance can land two levels up, which no generator margin covers; a
   trace that expects such a re-arm to fire within a short wait would be
   flaky, and the generator should compute the margin from the recorded
   level or avoid expecting those firings. Outside passes the lag is at most
   the softirq's latency and moves only the 2 s keepalive, one level.
5. **Placement of the wheel in `Kernel` versus `Env`**: the audit may prefer
   the pass in `Env.lean` since the tick triggers it; the split proposed here
   (arithmetic and pass in `Kernel/TimerWheel.lean`, the trigger and E1/E2 in
   `Env.lean`) follows AGENTS.md's line between the C's control flow and the
   fixture's timing.
6. **HZ-dependence**: the level thresholds assume `HZ=250` (`LVL_DEPTH 9`);
   they are constants of the pinned configuration, guarded by the identity
   check, and named in the module's header.

## 12. Estimate

Build, after the audit: the two kernel hooks, the checker sites and rules
0.5 d; `Kernel/TimerWheel.lean` with unit tests of the arithmetic against
the table in section 1.4, the same-slot path, the give-up deleting a
same-bucket keepalive, the two-pass stream and the equal-expiry order
1.5 d; `armTimer`, `delTimer`, the pass with its re-scan, E1 over passes,
the advance bound, E2's lookahead, `idleTimers`, `afterAdvance`, the
placeholder and the run-time invariants 1.5 d; the two new traces, the
claim point on the batch's rebuilt oracle, the seven one-off mutants and the
controls 1.5 d; docs and decisions 0.5 d: **5 to 6 agent-days, about 0.3 to
0.35 WU** (one WireGuard unit is about three weeks of parallel streams,
`docs/2026-10-12-kernel-scout.md`), with the instrument premium inside. The
campaign carry (section 10) is lane A's cost, two to four days, and the
oracle rebuild is the batch's.

## 13. Decisions

The user's:
- **U1.** Move the environment line as section 3.4 draws it: the firing set
  and order become the mirror's semantics (E1, over passes the stream
  bounds, in both directions); the tick's placement, the wait's tick count
  and the base clock stay recorded inputs. B3 delivers that, and **not** the
  plan's "kind-310/311 reads become derived" (section 4). This is the lane's
  go.
- **U2.** Two record-only hooks: kind 313 `{clk, timer}` in `__mod_timer`
  after `forward_timer_base` on both paths (`timer.c:1107`, `:1141`), where
  the C reads the clock, and kind 314 `{idx, bucket_expiry, timer}` in
  `enqueue_timer`; written without steering under `base->lock` (section 7).
  Class-approved by kind; flagged as the first records from the wheel's
  locked region. The no-new-site alternative is rejected in section 3.2.
- **U3.** `kernel/time/timer.c` stays unanchored and is declared "mirrored
  but unanchored"; the wheel's comparisons are checked by the kind-314
  record, not declared as decisions; its hooks may add lines (section 8).
- **U4.** E2 is `unsupported` (outside the timing domain) **only with the
  lookahead of section 3.4**: a due timer whose section appears later in the
  stream is the deferral; one whose section never appears is a hidden
  mismatch. Without the lookahead, U4 would let a mirror mistake pass as a
  host-timing outcome, and it is not proposed.
- **U5.** The layout of section 3.1: per-timer fields with an enqueue stamp
  (recommended, for the carry) or the per-base 576-slot array (the C's
  literal shape).

Tactical [AGENT]: the module (`Kernel/TimerWheel.lean`) and keeping
`Peer.timer*` and `armTimer`'s signature for the campaigns, the pass in
`Kernel`, the re-scan, the run-time invariants, the seven mutants and two
traces, the checker rules of section 6, the generator left as is, and the
probe of section 5.

## 14. Review dispositions

The review at `6fe87f2` (16 findings). Each is fixed in this revision,
answered with a reason the user can check, or raised for the user.

1. The same-slot decision read off the record's presence (blocking):
   **fixed.** Kind 313 records `base->clk` after `forward_timer_base` on
   both `__mod_timer` paths (`:1107`, `:1141`); the mirror computes the
   decision from state and kind 314 checks it (section 3.2, U2). The
   no-new-site rule is rejected with the reason there.
2. E1 as one pass at `J_end` (blocking): **fixed.** E1 is restated over
   passes the stream bounds, with the four constraints, the `T W N T` stream
   shown accepted, work between passes arming or deleting handled by the
   live wheel (section 3.4), a unit test and a trace (section 9).
3. The absorbing tick after an advance and the timer control: **fixed.**
   `J_pass = before` when `J_end = after`; the control's outcome re-derived
   from it (sections 3.4, 6).
4. E2 not exact, trigger misdescribed: **fixed.** E2 by lookahead (later
   section: `unsupported`; never: hidden mismatch); the trigger restated
   (one jiffy at HZ 250, `need_resched`, ten rounds; sections 1.3, 3.4); U4
   made conditional on the lookahead (section 13).
5. The clock's lead and the catch-up lag; "one place", "a level up":
   **fixed.** Section 1.2 states the lead of one and the catch-up lag;
   section 1.4's last paragraph and risk 11.4 corrected; the checks of step
   3 strengthened (`clk <= B` when a modeled bucket is overdue, `clk >= B + 1`
   inside a pass); the trace `d3_keepalive_rearm_catchup` and mutant B3-M7
   added (section 9).
6. B3-M2 not rejectable: **fixed.** Replaced by `LVL_START(4)` as 135001,
   rejected at every session trace's zero-key arm (section 9).
7. Per-timer bucket expiry, the re-scan, the run-time invariant: **fixed.**
   Section 3.1 states the stored bucket expiry with the aliasing reason and
   the invariants as run-time checks including `retirePeerUnits`; section
   3.3 re-scans after each callback with the three outcomes; a unit test
   for the give-up deleting a same-bucket keepalive (section 12).
8. The lock-context argument: **fixed.** Revision 1's reason withdrawn; the
   hooks use the mode check and `kcov_choice_write` without steering as the
   kind-304 writer does (`gen-choice-stream.py:995-1000`); both records carry
   the timer's address and the checker pairs them with their kind-303
   record (sections 6, 7).
9. The measurement weaker than its summary and not reproducible: **fixed.**
   The probe is committed (`scripts/probes/b3-wheel-replay.py`) with an exact
   deletion model at the C's sites, no absorption rule, every predicted-due
   timer without a section reported by disposition, the suite rerun on s4
   and the figures taken from it (section 5); the dump deleted, the command
   kept.
10. The departure from the plan's B3 line: **fixed.** Stated in sections 0,
    4 and U1 with the reasons for each read.
11. "Last armed first": **fixed.** "Last enqueued first" in sections 0, 1.3
    and 2.
12. "Highest level first at one step" unexercised: **fixed by stating it.**
    The order is kept as the C's, covered by a unit test; the note says the
    live corpus has no witness and why a trace cannot be forced (section 9).
13. The carry underestimated; `WGKernelView`; the per-timer alternative:
    **fixed.** Two to four days, `WGKernelView`'s 54 files named, the
    per-timer layout discussed and recommended, the choice raised as U5
    (sections 3.1, 10, 13).
14. U3's boundary: **fixed.** `timer.c` declared "mirrored but unanchored";
    the line-adding hooks and the coupling stated (sections 8, 13).
15. The estimate: **fixed.** Five to six agent-days, 0.3 to 0.35 WU
    (section 12).
16. Lane E's gain narrower than worded: **fixed.** Section 6 states the gain
    as the must-fire direction over accepted runs, with the level from the
    recorded clock and level 5 reachable in a long catch-up pass.

## 15. Build results (2026-10-15) [AGENT, fork of the coordinator]

The build follows this note as revised, on `task/design-b3`, one commit per
step. Decisions: U1 to U5 as recorded at `2784166` [USER 2026-10-15: approved
as proposed], U5 the per-timer layout with the enqueue stamp.

### 15.1 The oracle pair (step 1)

`kernel-net-choice-s5`, identity
`b44d958f09743feddc5fdbc3410cb5de89cead4bffdd62b06582b0c560454767` (patch
sha256 `630b602a…`), and `kernel-net-choice-actl-s5`, identity
`aa192fdc560e260d13f469f8cea4fc99a44a9bfaa2eb522c864c3014fa198120` (patch
`ab3a39ef…`); `kernel/config-x86_64-net-choice` unchanged; no anchored file
touched. The hooks are as section 7 says, with the placement note there:
kind 313 after `forward_timer_base` on both paths (`timer.c:1107`, `:1141`),
kind 314 at `__mod_timer`'s enqueue statement, both written with the mode
check and `kcov_choice_write` without steering, gated by the armed set and
`KCOV_DISPATCH_ARM_RECORDS`, carrying the timer's address; `__mod_timer`
receives its caller's return address from its six callers.

### 15.2 The stop risk: the wheel on the new records (the probe)

`scripts/probes/b3-wheel-replay.py` over the `wireguard` suite's dump on s5
(261 traces, 156 with arms), the base clock taken from kind 313 and the
kernel's slot and bucket expiry compared with the probe's arithmetic:

| Measured on s5 | Count |
| --- | --- |
| Arm records (kind 303) | 849 |
| Base-clock records (kind 313) | 755, one per arm that locked the base (the 94 same-expires returns wrote none) |
| of which the base clock is one ahead of `mod_timer`'s read (the lead after a pass of any owner) / behind it | 53 / 0 |
| Enqueue records (kind 314) | 593: every fresh placement and move (90), none of the 163 same-slot re-arms |
| **Enqueues whose slot and bucket expiry equal the probe's arithmetic** | **593 of 593** |
| **Firings predicted as the next to run (set and order)** | **46 of 46**, in 40 of 40 operations, the five multi-timer passes included |
| Due timers without a section, by disposition | 0 deferred, 0 unexplained |
| Deletions performed at the C's sites | 120 (handshake complete 94, data received 1, initiation sent 1, the transmit worker 10, `wg_down` 9, `wg_delete` 5), 0 ambiguous |
| The between zone | 2 of 2, correctly not fired |

The stop risk of section 11 did not occur on the new records: the wheel fed
with the recorded clocks predicts every firing, and the kernel's own slots
agree with the arithmetic at every enqueue.

### 15.3 The mirror, the environment and the validation (steps 2 to 5)

The build: `Leanux/Kernel/TimerWheel.lean`, the per-timer layout, `armTimer`
over the three paths with kinds 313 and 314, E1 over stream-bounded passes
and E2 by lookahead in `Leanux/Env.lean`, the two traces, the unit tests
(`leanux-timer-wheel-tests`, 23 checks) and the firing controls on an s5
capture (`TimerWheelFiring`, 3 tests). The five unit-test modules: 127
tests OK. The suite, control and mutant figures:

**The suite.** The `wireguard` suite on s5 with the finished model and the
two new traces: 263 traces, 1802 operations, status **pass**, 263
agreements, 0 failures (4 chunk splits on the contended host, no trace
rerun). `d3_two_passes` runs its two passes in one wait (the stream
`WWNTWWNTWWN`: the batch's workers, then the keepalive's pass with its
workers and NET_RX, then the second pass); `d3_keepalive_rearm_catchup`
records the lag (a base clock of 4294896320 against `mod_timer`'s read of
4294898126, 1806 ticks) and the re-arm on level 3, then the persistent
keepalive's firing in the same pass (`TTWWNNW`). An earlier run of the
suite, before `requireNothingDue` was guarded for a trace without wg0,
stopped 79 lifecycle traces with "no WireGuard device" and lost 9 traces to
`trace_exceeds_rekey_bound` under a host load of 50; both are in the
history of this branch, neither in the figures above.

**The probe on the clean dump.** 867 arms; 766 base-clock records (one per
arm that locked the base; 101 same-expires returns wrote none), 35 of them
one ahead of `mod_timer`'s read and 1 behind (the catch-up trace's lag);
608 enqueue records, 607 of 607 compared equal to the probe's arithmetic
(159 same-slot re-arms wrote none; 94 moves and every fresh placement
wrote one); 49 of 49 firings predicted as next in 42 of 42 operations, six
of them multi-timer passes; 0 due timers without a section; the between
zone 2 of 2; 122 deletions at the C's sites. The probe's one problem is its
own: `l_remove_readd_queued` removes a peer by `wg_set` and re-adds it at
the same address, a `wg_timers_stop` the probe's header says it does not
model, so it took the fresh arm's enqueue record for one on a kept slot;
the mirror, which performs that deletion, agrees on the trace.

**The timer control.** `tc_advance_wait0` with the guest variant
`advance-wait-0` on s5: rejected, `hidden_mismatch` ("a record of site 104
was not consumed" at the `wg_get`), inside its accepted set and as section
6 derives: with `J_end = after` the pass bound is `before`, nothing is due
at the advance, and the keepalive's section lands in the next operation.

**The mutants**, each run once on s5 by `scripts/wg-mutants.py`, then the
entries removed as the rule says (none replaces a sentinel's channel):

| Mutant | Subset | Result |
| --- | --- | --- |
| B3-M1, `calc_index` rounding down | `d3_persistent_k` | rejected, hidden mismatch (the kind-314 bucket expiry) |
| B3-M2, `LVL_START(4)` as 135001 | `d3_persistent_k` | rejected, hidden mismatch (the kind-314 slot at the zero-key arm) |
| B3-M3, FIFO within a slot | `w12_retransmit_lifo` | rejected, hidden mismatch (the section names the other peer's timer) |
| B3-M4, the must-fire direction dropped (`requireNothingDue` a no-op) | the evaluator control `TimerWheelFiring` | rejected: the two altered-capture tests do not pass under the mutant (the capture with the section removed and the one with it moved are both accepted), and pass after the revert |
| B3-M5, the same-slot path gone | `d2_padding_mtu` | rejected, hidden mismatch (a kind-314 record expected where the kernel kept the slot). On its first subset, `d3_persistent_k`, it **survived**: those traces' re-arms all move slots (every 1250-tick re-arm lands in a new 64-tick bucket), so the channel has no witness there; `d2_padding_mtu` has five same-slot re-arms |
| B3-M6, `expires` as the due test | `d3_between_zone` | rejected, hidden mismatch (the zero-key timer "did not fire", its section never appearing) |
| B3-M7, the base clock taken as `mod_timer`'s read | `d3_keepalive_rearm_catchup` | rejected, hidden mismatch (the kind-314 slot: level 2 computed, level 3 recorded) |

The unit tests: the five modules, 127 tests OK (1 skipped, as before);
`leanux-timer-wheel-tests`, 23 checks, 0 failures.

### 15.4 The proof frames for the integration record (read-only)

On `proofs/campaign`: 37 files name a changed or removed timer function
(`armTimer`, `delTimer`, `fireTimer`, `runTimers`, `runTimersPlaceholder`,
`idleTimers`, `afterAdvance`, `runTimerSection`, `timerCallback`), 10 of
them `fireTimer`, which no longer exists; 34 files name `WGKernelView`
(`Kernel` gained the scalars `timerClk` and `timerEnqueues`); 3 files build
a `Peer` literal and 2 name its timer fields (`Peer` gained five
`wheel*` fields and `World` three fields). On `proofs/campaign-2`: 9 files
name the timer functions (3 of them `fireTimer`), 1 builds a `Peer` literal,
none names `WGKernelView`. The counts are `git grep -l` over `Leanux/Proofs`
on each branch; the review's 54 for `WGKernelView` counted differently.
No file under `Leanux/Proofs/` was edited.
