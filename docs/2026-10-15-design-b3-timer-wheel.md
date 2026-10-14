# B3 design: the timer wheel as a mirror — 2026-10-15

Status: design note for stream B3 of
[the parallel plan](2026-10-14-wireguard-parallel-plan.md), written for the
user to read before anything is built, since it moves the environment line.
Docs only; the measurement in section 5 is read-only on the s4 oracle.
Nothing here is built, and nothing in `Leanux/` changes with this note.

## 0. In ten lines

Today the mirror holds each WireGuard timer as an expiry and learns *which*
timers fired, and in what order, from the records: each firing is a dispatch
section that names its timer, accepted if the timer is pending and its expiry
is before the end-of-wait clock read. The kernel's wheel (`kernel/time/timer.c`)
decides both from arithmetic: a timer lands in a bucket whose width grows with
its delay, fires at the first tick at or after the bucket's expiry, and
several due timers run in bucket order, highest level first, last armed first
within a bucket. B3 puts that wheel into the mirror at the thin layer, so the
firing set and order become semantics checked against the sections, with one
new record-only hidden input (the base clock at an enqueue, kind 313), and the
tick's placement in the trace stays the environment's. Section 5 measured it
on the s4 oracle: fed only the recorded clocks, the wheel predicts all 46
firings in 40 passes, their sets and their order, and the one case where a
timer in the window must not fire; section 11 names the risk that would have
stopped the stream, which did not occur. Cost about 0.25 WU to build, plus
the largest proof carry in the plan.

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
  wheel's own clock, in jiffies), `next_expiry` (the earliest pending
  bucket's expiry), `next_expiry_recalc`, `timers_pending`,
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
  when some bucket is already due (`:1008-1014`). **So `clk` lags `jiffies`
  exactly when a timer, of any owner, is due and its softirq has not run.**
- The slot: `calc_wheel_index(expires, clk)` (`:584-620`) picks the level
  from `delta = expires - clk` by the `LVL_START` thresholds (`:590-605`);
  `(long) delta < 0` is the past (`idx = clk & 63`, `bucket_expiry = clk`,
  `:606-608`); and `calc_index(expires, lvl)` (`:567-582`) rounds up:
  `e' = (expires >> 3·lvl) + 1`, `bucket_expiry = e' << 3·lvl`,
  `idx = 64·lvl + (e' & 63)` (`:579-581`). A timer therefore fires no earlier
  than `expires + 1` and no later than `expires + 8^lvl` ticks.
- Pending path: `clk = base->clk; idx = calc_wheel_index(...)`
  (`:1115-1116`); the same slot as before → only `timer->expires` is updated
  and the list position is kept (`:1123-1130`). Otherwise `detach_if_pending`
  (`:1144`), `timer->expires = expires` (`:1173`), and `enqueue_timer`
  (`:1180-1183`; through `internal_add_timer`, `:682-688`, if the base moved
  meanwhile, which it cannot on one CPU).
- `enqueue_timer` (`:655-680`): `hlist_add_head` (`:659`: last in, first
  out), set the pending bit (`:660`), store the slot in `flags` (`:661`),
  `trace_timer_start(timer, bucket_expiry)` (`:663`), and lower
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
  (`:2502-2504`). The tick device is periodic (D3, section 4.5, Q1).
- At interrupt exit, `__irq_exit_rcu` runs the pending softirqs unless the
  interrupted context was in interrupt or had bottom halves disabled
  (`kernel/softirq.c:652-666`, `:661-662`); otherwise they run at the next
  `local_bh_enable` or in ksoftirqd. `handle_softirqs` (`:536-610`) snapshots
  the pending mask (`:553`), clears it (`restart:`, `:559-560`) and runs the
  vectors in bit order (`:567-583`): `TIMER_SOFTIRQ` is bit 1 and
  `NET_RX_SOFTIRQ` bit 3 (`include/linux/interrupt.h:557-566`), so **within
  one pass the timer vector runs before the NET_RX vector**; a vector raised
  during the pass is served in the next round (`:596-600`), at most 10
  rounds or 2 ms (`MAX_SOFTIRQ_RESTART`, `MAX_SOFTIRQ_TIME`, `:500-501`),
  after which ksoftirqd takes over (`wakeup_softirqd`, `:602`).
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
  the dispatch section (D3, section 3.1).

So, at the first tick with `jiffies >= B`, every bucket with expiry `<= jiffies`
is run in ascending bucket expiry, levels collected at one step highest first,
each bucket last-armed-first. W12 Part II read the same order from the same
lines (`docs/2026-10-06-w3-w12.md`, section II.2) and was not built because the
dispatch-order records made it unnecessary (section V); B3 builds it because the
plan now wants the order as semantics.

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

A 2 s interval sits four ticks below the level-1/level-2 boundary (504): a
`clk` lag of four ticks at its arm moves it to level 2. That is the one place
in the corpus where the lag of section 1.2 changes the bucket width.

## 2. Today's mirror versus the C

| | Mirror today | C |
| --- | --- | --- |
| Timer datum | `Peer.timer* : Option UInt64`, `some expires` while pending (`Types.lean:309-321`); `timer_pending` is `isSome` | `timer->expires`, the slot in `flags`, membership in a list |
| Arming | `armTimer` (`State.lean:145-168`): consumes the caller's read J_c (kind 311) and the arm record `{J_m, expires, timer}` (kind 303), checks `expires = J_c + delay` and `J_m − J_c ∈ {0, 1}`, stores `expires`, keeps the timer's address for its section | `__mod_timer`: same-expires return, forward the base, compute the slot, keep position or re-enqueue at the head |
| Deleting | `delTimer`: the field to `none` | `detach_if_pending` |
| Which timers fire, in what order | **the records**: at an idle point, `runTimers` consumes each timer section in record order; `fireTimer` accepts it iff the named timer is pending and `time_before(expires, J_end)` (`Env.lean:364-397`); a due timer with no section is not an error (the trace's `expect` label catches it) | the pass of section 1.3: every bucket with expiry `<= jiffies`, in bucket order |
| The window | the end-of-wait read J_end (kind 310, review item 7) bounds the firings | the softirq's `jiffies` at the pass |
| Several same-kind timers in one pass | the order the records show (W12 results, dispatch-order) | ascending bucket expiry, level, LIFO |
| A timer whose `expires < J_end` but bucket expiry `> J_end` | fires or not, "benign, the mirror follows the sections" (`d3_between_zone`, D3 section 17.3) | does not fire |
| Domain filter (no records) | `runTimersPlaceholder`: earliest `expires` first | n/a |

The mirror's rule is sound in one direction (a section is accepted only for a
timer that could be due) and silent in the other (a due timer that did not
fire is not reported by the mirror). The order is an input, not a prediction.

## 3. The change at the thin layer

### 3.1 State: the base restricted to the armed set

A new module `Leanux/Kernel/TimerWheel.lean` (kernel code, like the dispatch
state in `Defs.lean`; not `Env.lean`), with the C's shapes:

- `TimerRef := PeerId × PeerTimer` (the `timer_list` the peer embeds).
- `TimerBase` (`timer.c:251-266`, the modeled subset): `vectors : Array
  (List TimerRef)` of 576 slots, each list head first (`hlist_add_head`);
  `slot : Std.HashMap TimerRef Nat` (the slot stored in each timer's `flags`,
  `timer_set_idx`); `clk : UInt64` (the base clock as last recorded, section
  4). `pending_map` is "the slot's list is nonempty" and needs no field;
  `next_expiry` is not represented (section 3.4 says why that is exact for the
  subset).
- `Peer.timer* : Option UInt64` stays as `timer->expires` while pending, so
  the campaigns' frames over those fields keep their types; the invariant
  "`(p.timer t).isSome ↔ (pid, t)` is in a slot" is maintained by the three
  operations below and checked by the unit tests. `Peer.timerPending` keeps
  its definition.

### 3.2 Arming: `modTimer` as `__mod_timer`

`armTimer pid t delay jc?` keeps its signature and its two checks, then runs
the C's paths on the wheel instead of only storing the expiry:

1. `expires := J_c + delay` (as today, checked against the arm record).
2. If pending with the same `expires`: return (`:1083-1088`); nothing else
   changes (no enqueue, so no kind-313 record: section 4).
3. The base clock at this arm is the recorded `clk` of the kind-313 record
   (section 4), checked: `time_before_eq(clk, J_m + 1)` (the forward reads
   `jiffies`, at most one tick past `mod_timer`'s read) and `clk` never
   behind the previous recorded `clk` (`__forward_timer_base` never rewinds);
   a violation is a hidden mismatch.
4. `(idx, bucketExpiry) := calcWheelIndex expires clk` (`:584-620`,
   `:567-582`), on `UInt64` with the C's `time_before`.
5. If pending and `idx` is the timer's current slot: update the expiry, keep
   the position (`:1123-1130`); no record.
6. Else detach if pending (`:1144`), set the expiry (`:1173`), push at the
   head of `vectors[idx]` (`:659`), store the slot (`:661`), and consume the
   kind-313 record, whose `idx` and `bucket_expiry` must equal the mirror's
   (a difference is a wrong wheel arithmetic in the mirror: a hidden
   mismatch, the channel of mutants B3-M1 and B3-M2).

`delTimer` becomes `detach_if_pending`: remove from its slot's list, clear the
expiry. `peerRemoveAfterDead`'s `wg_timers_stop` deletes the five as today.

### 3.3 The pass: `__run_timers` at a jiffies value

`runTimerPass J` (the C's `:2390-2422` over the modeled subset): while some
slot holds a timer with `bucket_expiry <= J` (the C's `jiffies >=
next_expiry`), take the smallest bucket expiry; of the slots at that expiry,
run the highest level first (`:2419-2420`); run each list head first
(`:1813-1852`); for each timer: detach it (`:1829`), then `call_timer_fn` is
the section: the next record must start that callback's section and name
this timer (its address from the arm record, as `fireTimer` resolves today);
any other next record is a hidden mismatch ("the wheel fires peer A's
retransmit next; the records show …"). Then the callback (`WG.timerCallback`,
unchanged). The pass ends when no modeled bucket is due.

Why `next_expiry` over the full wheel is not needed: the C's loop steps
`clk` through every pending bucket expiry `<= jiffies` in ascending order,
whatever its owner, so a modeled bucket with expiry `B <= jiffies` is
collected at the step `clk = B` of the first pass whose `jiffies >= B`
(section 1.3). Unmodeled timers change which steps exist, not whether or
when a modeled bucket is run. They do change `base->clk` at an arm, which
is why `clk` is recorded.

A callback's re-arm during a pass is `expires = jiffies + delay > jiffies`,
never due in the same pass (D3 section 2.3, item 3); its slot is computed
with the recorded `clk`, which inside a pass may be `next_expiry` of a later
bucket still due (`:1008-1014`) — the record carries it.

### 3.4 The firing rule at idle points, redrawn

`idleTimers` and `afterAdvance` keep their place (the guest's waits after
`wg_set`, `wg_up`, `wg_inject`, `wg_xmit`, `wg_batch`, before `wg_observe`,
and after `wg_advance`, `Syscalls.lean:383-391`) and their kind-310 read
`J_end`. The rule becomes:

> **E1.** Every modeled timer with `bucket_expiry <= J_end` has fired before
> the read, by `runTimerPass J_end` in wheel order; no timer with
> `bucket_expiry > J_end` has. The sections are checked against the pass.

The two directions today's rule lacks are now exact: a timer with
`expires < J_end` but `bucket_expiry > J_end` must **not** have a section
(`d3_between_zone` becomes a rule, not a 3 % lottery), and a due timer
**must** have one. Work the callbacks queue runs as today (`runTimers`'
tail: the send and clear workers, the crypt workers, `deliverSent`).

Using `J_end` for the pass is exact because a tick between the last pass
and the read would have run another pass before the task resumed
(`__irq_exit_rcu`, `:661-662`: the guest is in task context with bottom
halves enabled during its wait and its read), with one exception, E2.

> **E2.** A due timer without its section before the read is the softirq
> deferred to ksoftirqd (`handle_softirqs` exhausted its 2 ms or 10 rounds,
> `softirq.c:596-603`) past the read: `unsupported "a due timer's softirq
> deferred past the end-of-wait read"`, outside the fixture's timing domain,
> like the two-read gap above one tick (review item 8).

The tick's **placement** in the trace is unchanged and stays the
environment's: a timer section at a non-idle point (inside a worker's body or
a syscall) remains a hidden mismatch (D3 section 5.3), since the mirror cannot
run a callback mid-body; the section's position in the stream is the only
record of where the tick landed, and no new record is proposed for it.

### 3.5 The timer softirq relative to NET_RX

What determines it (section 1.3): the tick raises `TIMER_SOFTIRQ`; NET_RX is
raised by the data path (a loopback transmit from a worker, an injected
datagram). In one `handle_softirqs` pass the timer vector runs first; a tick
that lands inside a NET_RX section raises the timer vector for the next round,
after the NET_RX action returns. At an idle point no NET_RX work is pending
when the tick fires (the operation's own waits drained it), and the NET_RX
sections that follow a timer pass come from the work its callbacks queued (a
keepalive's encrypt and transmit workers, whose loopback send raises NET_RX
at the worker's `local_bh_enable`), so they follow the worker sections in the
stream. The mirror already runs that tail in record order. **No new record and
no new rule**: the relative placement is forced by the data flow at idle
points, and a tick inside a NET_RX section is the mid-body case of section
3.4. Section 5 measures the observed pattern.

### 3.6 The domain filter

`runTimersPlaceholder` (no records) runs `runTimerPass` with `clk = the last
known jiffies` at every arm and the fixture's window (`Timing`), so its
prediction is the wheel's order rather than earliest-expiry-first.

## 4. Records: what stays, what is checked, what is new

| Record | Today | After B3 |
| --- | --- | --- |
| kind 311, the caller's `jiffies` read | hidden input | **stays**: the clock WireGuard reads |
| kind 303, `{J_m, expires, timer}` at `mod_timer` | hidden input; expiry check; the timer's identity | **stays**: the expiry check (D3-M8's channel) and the identity |
| kind 304, the advance | hidden input | **stays**: the operation's effect on `jiffies_64` |
| kind 310, the end-of-wait read | the window's end for `expires < J_end`, accept-only | **stays, consumer changed**: the pass's `jiffies` for E1, both directions. It cannot be derived: how many ticks a wait took is a clock, and the fired set alone would only bound it (accepting any downward-closed set is the fail-open rule B3 removes) |
| kind 300/301, the sections | the firing choice: which timer, in what order | **checked, not chosen**: the section must be the pass's next timer; the callback's records still live inside it |
| **kind 313 (new)**, `{base->clk, idx, bucket_expiry}` at `enqueue_timer` for the armed set | — | the base clock at the arm (a hidden input: it depends on timers outside the modeled set) and the C's slot, which checks the mirror's arithmetic; absent on a same-slot re-arm, which checks the position-kept path |

The environment line after B3: the mirror owns the wheel's slots, the arm
paths, the pass and its order; the environment owns the tick's placement (the
section's position, idle points only), the number of ticks a wait took
(kind 310), the base clock's lag (kind 313), and the deferral case (E2).

## 5. Measurement on s4

Method: the `wireguard` suite run read-only on the s4 oracle (identity
`6b2018b9…`) from this worktree
(`.artifacts/check/b3-measure`, ephemeral), and an ephemeral script
(`.artifacts/b3/wheel.py`, not committed) that replays each trace's choice
records of the coverage child in sequence order, feeding the wheel arithmetic
of section 1.2 with only the recorded clocks: at each kind-303 record it
places the timer (`clk = J_m`, the no-lag case, since kind 313 does not exist
yet), applies the same-slot and re-enqueue paths, and at each operation with a
kind-310 read predicts the fired set `bucket_expiry <= J_end` in the wheel's
order and compares it with the timer sections' order (the timer named by each
section's unit word). Deletions are not recorded, so a timer the wheel
predicts due that never fires and is later re-armed is counted as deleted;
one that fires in a later operation is counted as a late firing.

**Run.** 261 traces of the `wireguard` suite (the corpus and 200 generated),
status pass on s4, 2026-10-15 from this worktree; 156 traces arm a timer.

| Measured | Count |
| --- | --- |
| Arm records (kind 303) | 847 |
| of which a pending timer re-armed with the same `expires` (`__mod_timer`'s early return, no wheel change) | 100 |
| of which a pending timer re-armed into its own slot (position kept) | 161 |
| of which a pending timer moved to another slot (re-enqueued at the head) | 91 |
| Fresh or moved placements by level: 1 / 2 / 3 / 4 | 3 / 304 / 162 / 117 |
| End-of-wait reads (kind 310), i.e. idle points | 1312 |
| Advances (kind 304) | 44 |
| Timer sections (firings) | 46, in 40 operations |
| Operations with several firings in one pass | 5 |
| **Firings the wheel predicts as the next to run, with the fired set and order** | **46 of 46** |
| Operations whose firings the wheel predicts exactly | 40 of 40 |
| Firings in a later operation than the read that made them due (the deferral, E2) | 0 |
| Timer sections in an operation without a kind-310 read | 0 |
| Timers with `expires < J_end` and `bucket_expiry > J_end` (the between zone) | 2, both `d3_between_zone`'s zero-key timer, correctly not fired |
| Arms while a modeled timer was overdue (the `clk` lag the records can see) | 0 |
| Operations with both timer and NET_RX sections | 32, in every one the timer sections precede the NET_RX ones |

The five multi-firing passes are `w12_retransmit_lifo` (two retransmits, the
later-armed first), `w12_three_retransmit` (three, last-in-first-out),
`d3_zero_key` and `l_delete_after_clear_work` (the persistent keepalive's
level-3 bucket, then the zero-key timer's level-4 bucket, ascending bucket
expiry) and `d3_zero_key_after_new_handshake` (the new-handshake timer, then
the zero-key timer). Their section patterns are timer sections first, then
the workers the callbacks queued, then the NET_RX sections their loopback
sends raise (`TTW`, `TTWNW`, `TTWNWN`, `TTTWNWNWN`), as section 3.5 says.

Two timers the script predicted due never fired, both deletions the records
do not carry and the mirror's control flow performs: the keepalive re-arm
that the transmit worker's `wg_timers_any_authenticated_packet_sent` deletes
(`d3_keepalive_rearm_deleted`, the D3 control built for exactly this) and the
retransmit timer `wg_timers_stop` deletes at `wg_down`
(`l_down_stops_timers`). The handshake-completion deletion
(`timers.c:194`) was resolved in the script from its kind-205 clock record at
`receive.c:179` and `:347` (94 of them); without that, the deleted retransmit
timer sat ahead of 17 observed firings in the script's queue, each of which
was the wheel's next after it.

**Verdict.** On this oracle, the wheel's arithmetic fed only the recorded
clocks (`clk = J_m`, the no-lag case) predicts every observed firing, every
fired set at every idle point, and every order, including all five
multi-timer passes and the between zone. No deferral past a read was seen in
1312 idle points. What the records cannot show is the `clk` lag from timers
outside the modeled set (section 1.2): none of the 847 arms needed one to
match, which bounds its effect on this corpus at zero observed level changes;
kind 313 makes it recorded rather than assumed. The stop risk of section 11
did not materialise.

## 6. Effects

- **Key lifetime over the wheel (campaign 3, lane E).** Today R5's time half
  rests on recorded clocks and the recorded sections ("no Linux schedule
  claim"). With the wheel the mirror carries the C's bound: a zero-key timer
  armed at `J_c` with `expires = J_c + 135000` and recorded `clk` lands on a
  level the mirror computes (level 4 at `clk ≈ J_c`, width 4096), and under
  E1 its callback runs at the first idle point whose read reaches the bucket
  expiry, so the clear work is queued within `REJECT_AFTER_TIME·3·HZ + 8^lvl`
  ticks of the arm's read unless an arming site re-arms or a deleting site
  deletes it. That is the statement campaign 3 can pose over the mirror
  ("key lifetime over the timer wheel" in the plan), conditional on the
  liveness premise that `jiffies` reaches the bucket expiry at an idle point.
- **The D3 corpus** (`d3_*`, `w12_*`, `tc_advance_wait0`, the keepalive
  traces): no trace changes. Every pass is now checked both ways; the
  `expect: fired:` labels become redundant with the rule but stay as the
  trace's intent. `d3_between_zone` turns exact. `w12_retransmit_lifo` and
  `w12_three_retransmit` check the LIFO order against the sections instead
  of taking it from them. The generator's `fire_advance`/`quiet_limit`
  margins (`evaluator/generate.py:1425-1447`) stay as heuristics; they could
  later ask the mirror's wheel for the exact advance, which is not part of B3.
- **The timer control** `tc_advance_wait0` still fails in its stated way (its
  sections land in a non-idle operation).
- **The checker**: `jiffies_problems` (`evaluator/check.py:679-750`) gains
  kind 313 (24 bytes; `clk` never goes back; `clk <= J_m + 1` of the
  preceding 303), and a new site `HiddenSite.timerEnqueue` (kind class
  `wheel`, resolved by kind like 304 and 310, since `enqueue_timer` has no
  caller frame of ours). `kernel/time/timer.c` stays unanchored.

## 7. Oracle changes

One change, record-only, under the approved class: in `enqueue_timer`
(`timer.c:655-680`), beside `trace_timer_start`, a call
`kcov_timer_enqueue(timer->function, base->clk, idx, bucket_expiry)` that
writes kind 313 `{clk, idx, bucket_expiry}` (24 bytes) for a function in the
armed set, with the same lock-free membership test as `kcov_timer_arm`
(`gen-choice-stream.py:798-827`). It runs under `base->lock` with interrupts
off; the writer takes no lock of its own (`kcov_choice_write_area`, patch
`:219-262`) and the steering lookup's leaf lock is already taken under the
timekeeper locks by the kind-304 writer, so this is the same context class.
No configuration or behaviour change; no new boot parameter. The identity
and patch hash land with the batch's rebuild, as the rule says.

Flagged for the user, not because it changes behaviour but because it is the
first record written from inside the wheel's locked region: if the audit
prefers, the same information can be recorded lock-free in `mod_timer` after
`__mod_timer` returns, as `{ret, timer->expires, timer_get_idx(timer)}`; that
variant loses `base->clk` (the level is then the recorded fact and the lag is
inferred, not recorded) and the absence-on-same-slot check. I recommend the
`enqueue_timer` hook.

## 8. Decisions and operands

The wheel's comparisons (`calc_wheel_index`'s nine thresholds, the
same-expires and same-slot tests, the pass's `time_after_eq` loop) are in
`kernel/time/timer.c`, which is not an anchored file (`correspondence/
kcov.json` anchors `drivers/net/wireguard/*` and the FS files), so they get no
KCOV witness and no comparison record, and the mirror implements them as
plain Lean on `UInt64` with the C's `time_before` family, **not as declared
`Decision`s**. The check of the arithmetic is the kind-313 record: `idx` and
`bucket_expiry` are the C's computed results, compared for equality at every
enqueue, which is a stronger check than a branch witness. Anchoring
`timer.c` (line-preserving hooks for its decisions) is possible but buys a
witness for arithmetic the record already compares; I recommend against it.
WireGuard's own timer decisions (`timers.c:46, :60, :84, :110, :112, :140,
:147, :156-157, :214`) are unchanged.

## 9. One-off mutants (each run once in the build's commit, then deleted)

- **B3-M1**, rounding down: `calc_index` without the `+ 1`. Rejected by the
  kind-313 `bucket_expiry` on the first arm of every D3 trace.
- **B3-M2**, a level threshold off (`LVL_START(2)` as 512): rejected by the
  kind-313 `idx` on the retransmit's arm (`d3_retransmit`).
- **B3-M3**, FIFO within a bucket (push at the tail): rejected by
  `w12_retransmit_lifo` (the section names B, the mirror's pass predicts A).
- **B3-M4**, the must-fire direction dropped (a due timer without a section
  accepted): no live trace changes verdict, so this one is an evaluator
  control on a replay capture with a timer section removed, like the
  allocation evaluator controls; rejected by the E1 report.
- **B3-M5**, position never kept (always re-enqueue): rejected by a kind-313
  record the mirror expects and the kernel did not write, on the persistent
  keepalive's traversal re-arms within one bucket (`c_keepalive_endpoint`,
  `d3_persistent_keepalive`).
- **B3-M6**, the between zone fires (`expires <= J_end` as the due test):
  rejected by `d3_between_zone` when its phase puts the bucket boundary past
  the read (about 97 % of runs; an inconclusive verdict otherwise, reported
  as such like Q-M1).

A sentinel is kept only if one of these replaces an existing channel; B3-M1
would replace nothing and stays one-off.

## 10. Proof-tree frames touched (read-only, `git show`)

Campaign 1 (`proofs/campaign`, 25 files, 588 theorems in them): every file
that names `armTimer`, `fireTimer`, `runTimers`, `runTimersPlaceholder`,
`idleTimers`, `afterAdvance`, `runTimerSection` or `timerCallback`. The
heaviest: `WG/Lifetimes/EnvTimersAudit.lean` (82 references),
`Logged/Operations.lean` (39), `WG/Lifetimes/EnvDeferredCalls.lean` (18),
`WG/Keypairs/Frames/Env.lean` (18), `WG/Keypairs/Evolution/Operations.lean`
(18), `WG/Lifetimes/MaintenanceTimers.lean` (12),
`WG/Environment/TimerSource.lean` (11: a literal restatement of `fireTimer`
closed by `rfl`, which must be rewritten against the pass),
`WG/Lifetimes/SyscallsAudit.lean` (10), `WG/Lifetimes/TimerCallbacks.lean`
(9), `Logged/Syscalls.lean` (8), `Logged/Advance.lean` (7), `Logged/TimerPass.lean`
(3), and `WG/KeyLifetime/Statements.lean` (1). The `Kernel` structure gaining
`timerBase` touches every full-`Kernel` frame that enumerates fields
(`Framing/WGKernel`'s seven-field projection and the frames built on it).
This is the carry the plan calls the largest; the campaign's lag-and-repair
rule applies.

Campaign 2 (`proofs/campaign-2`, 6 files): `Logged/Operations.lean`,
`Logged/Syscalls.lean`, `WG/Keypairs/Evolution/Operations.lean`,
`WG/Keypairs/Frames/{Env,WGBase,WGTransitions}.lean` — all shared layers
campaign 1 owns, so campaign 2 carries by merge. H6 (timer discipline) has no
files yet and "deliberately does not depend on" the wheel; its claims are
about arming sites and delays, which `armTimer` keeps (same signature, the
same two checks, one more record consumed), so H6 re-proves `armTimer`'s body
lemmas and nothing in its statements.

## 11. Risks, the stopping one first

1. **Stop risk: the wheel does not predict the s4 oracle.** If section 5
   shows firings the wheel fed with the recorded clocks does not predict
   (sections for timers whose bucket is not due, or an order not the wheel's)
   beyond what the no-lag approximation of `clk` explains, the pass is not a
   function of the recorded inputs and the lane stops at this note; lane E's
   key lifetime stays record-based, as the plan allows. **Measured: it did
   not happen.** 46 of 46 firings, 40 of 40 passes and both between-zone
   cases are predicted (section 5), so the stream can proceed.
2. **The deferral case (E2) is frequent under host load.** Then "every due
   timer fires before the read" would fail traces as `unsupported` at a rate
   the contended-host rule does not allow. Today such a firing lands in the
   next operation, which is already a hidden mismatch unless that operation
   is an idle point, so the rate is bounded by today's pass rate; section 5
   counts late firings directly.
3. **The carry on campaign 1** (section 10): one to two agent-days, the
   largest in the plan; mitigated by keeping `Peer.timer*`'s types and
   `armTimer`'s signature.
4. **The lag is larger than a tick more often than expected** (a 4 ms
   bottom-half-disabled region on the TCG guest): harmless to correctness
   once `clk` is recorded, but it would put a 2 s persistent keepalive on
   level 2 in some runs, so a trace that expects its firing within a short
   wait could become flaky; the generator's margins already cover a level
   up.
5. **Placement of the wheel in `Kernel` versus `Env`**: the audit may prefer
   the pass in `Env.lean` since the tick triggers it; the split proposed here
   (arithmetic and pass in `Kernel/TimerWheel.lean`, the trigger and E1/E2 in
   `Env.lean`) follows AGENTS.md's line between the C's control flow and the
   fixture's timing.
6. **HZ-dependence**: the level thresholds assume `HZ=250` (`LVL_DEPTH 9`);
   they are constants of the pinned configuration, guarded by the identity
   check, and named in the module's header.

## 12. Estimate

Build, after the audit: the kernel hook and checker site 0.5 d;
`Kernel/TimerWheel.lean` with unit tests of the arithmetic against the table
in section 1.4 1 d; `armTimer`, `delTimer`, the pass, `idleTimers`,
`afterAdvance`, the placeholder 1 d; the claim point on the batch's rebuilt
oracle, the six one-off mutants and the controls 1 d; docs and decisions
0.5 d: **4 agent-days, about 0.25 WU** (one WireGuard unit is about three
weeks of parallel streams, `docs/2026-10-12-kernel-scout.md`), with the
instrument premium already inside. The campaign carry (section 10) is lane
A's cost, one to two days, and the oracle rebuild is the batch's.

## 13. Decisions

The user's:
- **U1.** Move the environment line as section 3.4 draws it: the firing set
  and order become the mirror's semantics (E1), the tick's placement, the
  wait's tick count and the base clock's lag stay recorded inputs. This is
  the lane's go.
- **U2.** The kind-313 record at `enqueue_timer` (record-only, class-approved
  by kind; flagged in section 7 as the first record from the wheel's locked
  region). Alternative: the lock-free post-call variant.
- **U3.** `kernel/time/timer.c` stays unanchored; the wheel's comparisons are
  checked by the record, not declared as decisions (section 8).
- **U4.** E2 is `unsupported` (outside the timing domain), not a hidden
  mismatch, consistent with the two-read gap rule.

Tactical [AGENT]: the module and type shapes of section 3.1 (keeping
`Peer.timer*` and `armTimer`'s signature for the campaigns), the pass in
`Kernel`, the six mutants, the checker rules of section 6, the generator left
as is, and the measurement method of section 5.
