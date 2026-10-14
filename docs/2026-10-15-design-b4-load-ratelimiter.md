# B4 design: load as a recorded input, the ratelimiter's GC, the entry allocation — 2026-10-15

Stream B4 of [the parallel plan](2026-10-14-wireguard-parallel-plan.md)
(section 2, row B4). Design only; nothing here is built. Measured on the
s4 oracle (identity `6b2018b9…`), one trace at a time, in
`.worktrees/design-b4` [AGENT, fork of the coordinator].

## 0. Summary

Three questions, three answers:

1. **Under-load as a recorded input.** No new record kind. The kernel
   already records everything the under-load decision depends on: the
   compare's operands at `receive.c:112-113` (the comparison instrument,
   checked per distinct value), the clock read per packet at `:115`
   (site 130) and the decay read at `:117` (site 6), and the producer and
   worker sections with the queue and resched records. What is missing is
   that the mirror does not *use* them for the flood's tail: it summarises
   the tail (`floodTailEffect`) and the check skips the flood's decisions.
   The change is to retire the summary and the check's special case and run
   every flood packet through the real producer and worker, as `wg_batch`
   already does for data packets. Measured: the exact execution consumes
   the same 1,565 remote records the summary discards or folds, reports
   5,703 branches instead of one, matches 1,049 operand pairs instead of
   18 (every tail packet's counter against Linux's), and costs the mirror
   10 ms for the 520 packets (section 2.4).
2. **The GC.** It runs in every WireGuard trace today, about once a second
   from `wg_create`, unobserved: the work function is not in the dispatch
   set, so no section opens and nothing it does is recorded; the mirror's
   `gcEntries true` arm stops as unsupported but is never reached. Making
   it a dispatched unit needs two record-only hook changes in unanchored
   files (the firing section named after the delayed work's function, the
   arm record at `__queue_delayed_work`), one dispatch-set symbol, and one
   harness change that closes an instrument gap: the guest resets the remote
   area at every operation's start, so a section that lands between
   operations is lost. The GC's sections would land there often; the peer
   timers' never do only because of the trace bound.
3. **The entry allocation.** No kernel change: the kind-305 hook is
   generic (`slab_alloc_node`, armed by address ranges the harness resolves
   from a site table), so the "site not in the hook's list" wording of the
   E design is wrong. The site is a row in `harness/steer.py`'s
   `ALLOC_SITES` plus an `AllocSite` constructor; the failure arm becomes
   the C's `err_oom` drop, modelled, reachable only by steering a class the
   host does not enable. The init's three allocations stay outside the
   model, with the reason written (section 4.4).

Estimate: about 0.15 WU (three to four agent-days) for the build, half of
it the flood's exact execution and its corpus and controls, a quarter the
GC with its hooks and the guest's window change, the rest the allocation
site, the docs and the one-off mutants. The stop risk is the GC's
placement: a 1 Hz tick-driven unit that can land inside any task section
needs an ambient-section rule the mirror does not have today (section 11).

## 1. The C, verified against `.deps/linux` (6.12.110)

### 1.1 Under-load and the handshake queue (`receive.c`)

```c
/* wg_receive_handshake_packet, :92-132 */
under_load = atomic_read(&wg->handshake_queue_len) >=            /* :112 */
             MAX_QUEUED_INCOMING_HANDSHAKES / 8;                 /* :113 */
if (under_load) {
        last_under_load = ktime_get_coarse_boottime_ns();        /* :115 */
} else if (last_under_load) {                                    /* :116 */
        under_load = !wg_birthdate_has_expired(last_under_load, 1); /* :117 */
        if (!under_load)                                         /* :118 */
                last_under_load = 0;                             /* :119 */
}
mac_state = wg_cookie_validate_packet(&wg->cookie_checker, skb, under_load); /* :121-122 */
```

`last_under_load` is a function-local static (`:100`). The producer
(`wg_packet_receive`, softirq) tests `handshake_queue_len > MAX/2` for the
trylock path (`:554-558`), produces (`:560`), increments (`:567`) and
queues the worker (`:570-571`). The worker (`:206-218`) consumes
(`:212`), handles (`:213`), decrements (`:215`) and `cond_resched`s
(`:216`) per packet.

### 1.2 The ratelimiter (`ratelimiter.c`)

- `wg_ratelimiter_allow` (`:84-156`): the family switch (`:95-109`; IPv6
  keys by the first eight bytes, `:103`), the bucket walk with the exact
  `(net, ip)` compare (`:111-112`), on a hit the clock (`:121`), the token
  refill `min(TOKEN_MAX, tokens + now - last)` (`:122-124`), `ret = tokens
  >= PACKET_COST` (`:126`); on a miss `atomic_inc_return(&total_entries) >
  max_entries` (`:135`), `kmem_cache_alloc(entry_cache, GFP_KERNEL)`
  (`:138`), NULL to `err_oom` (`:139-140`), the insert's clock (`:146`),
  `tokens = TOKEN_MAX - PACKET_COST` (`:147`), the list add (`:149`);
  `err_oom` decrements the counter and returns false (`:153-155`).
- `wg_ratelimiter_gc_entries` (`:55-82`): one clock read (`:57`); for
  each of `table_size` buckets (`:62`): the v4 list (`:64-68`) and the v6
  list (`:70-74`), each entry uninitialised when `!work` or `now -
  entry->last_time_ns > NSEC_PER_SEC` (`:65-66`, `:71-72`;
  `entry_uninit` `:48-52`: `hlist_del_rcu` and a `call_rcu` free whose
  callback decrements `total_entries`, `:41-46`); `cond_resched` per
  bucket when `work` (`:77-78`); the requeue `queue_delayed_work(
  system_power_efficient_wq, &gc_work, HZ)` when `work` (`:80-81`).
- `wg_ratelimiter_init` (`:158-203`): `++init_refcnt != 1` (`:161`), the
  slab cache (`:164`), `table_size` from RAM (`:173-177`: 2048 on the
  fixture), the two `kvcalloc`s (`:179`, `:184`: 16 KiB each), the first
  `queue_delayed_work(…, HZ)` (`:191`), the siphash key (`:192`).
- `wg_ratelimiter_uninit` (`:205-221`): `!init_refcnt || --init_refcnt`
  (`:208`), `cancel_delayed_work_sync(&gc_work)` (`:211`),
  `wg_ratelimiter_gc_entries(NULL)` (`:212`), `rcu_barrier` (`:213`).
- `cookie.c:119-154`: MAC1 (`:130-133`), `VALID_MAC_BUT_NO_COOKIE` and
  the early out without `check_cookie` (`:135-138`), `make_cookie` and
  MAC2 (`:140-144`), `VALID_MAC_WITH_COOKIE_BUT_RATELIMITED` unless
  `wg_ratelimiter_allow` (`:146-148`), `VALID_MAC_WITH_COOKIE` (`:150`).

### 1.3 The delayed work and the configuration

`DECLARE_DEFERRABLE_WORK(gc_work, wg_ratelimiter_gc_entries)` (`:20`) is
a `delayed_work` whose timer has function `delayed_work_timer_fn` and
flags `TIMER_DEFERRABLE | TIMER_IRQSAFE` (`include/linux/workqueue.h:244-257`).
`queue_delayed_work` (`workqueue.h:676-682`) is `queue_delayed_work_on`
(`kernel/workqueue.c:2575-2595`): a `test_and_set_bit(WORK_STRUCT_PENDING_BIT)`
and, when it was clear, `__queue_delayed_work` (`:2524-2567`): `delay == 0`
queues at once (`:2541-2544`), else `timer->expires = jiffies + delay`
(`:2549`) and, housekeeping disabled on this config, `add_timer_global`
(`:2561`), which is `__mod_timer(…, MOD_TIMER_NOTPENDING)`
(`kernel/time/timer.c:1325-1331`) and so **bypasses `mod_timer`**, where the
kind-303 arm hook sits. The timer's callback `delayed_work_timer_fn`
(`workqueue.c:2515-2521`) is `__queue_work(dwork->cpu, dwork->wq,
&dwork->work)`. `cancel_delayed_work_sync` (`:4470-4474`) is
`__cancel_work_sync(…, WORK_CANCEL_DELAYED)` (`:4382`): grab pending
(deleting a pending timer), then `__flush_work` if the work runs.

The oracle's configuration (`kernel/config-x86_64-net-choice`): `HZ=250`,
`HZ_PERIODIC` (no `NO_HZ`: `NR_BASES = 1`, so `BASE_DEF` is the one base,
`timer.c:200-203`, and the deferrable flag changes nothing about
placement), `PREEMPT_NONE`, no `SMP`, `IPV6`, no
`WQ_POWER_EFFICIENT_DEFAULT` (`system_power_efficient_wq` is an ordinary
per-CPU workqueue, `workqueue.c:7876-7877`), no `CPU_ISOLATION`.

### 1.4 The instruments as they stand

- Clock reads are wrapped generically (`kernel/patches/gen-choice-stream.py:444-457`):
  every exported reader records `{kind 200+, _RET_IP_, value}`, attributed
  to the caller's frame. So `:57`, `:115`, `:117`, `:121`, `:146` are
  sites 124, 130, 6, 132, 133 already (`Defs.lean:1209,1290,1328,1332-1333`),
  written only in a recording context (`kcov_choice_write`: outside one,
  nothing, uncounted).
- Allocation outcomes, kind 305, are recorded by one hook in
  `slab_alloc_node` and one in `__alloc_pages_noprof`, gated by an armed
  range set the harness loads per chunk (`gen:1467-1516`,
  `docs/2026-10-05-a-alloc.md` 4.1-4.3). A site is a row of
  `harness/steer.py`'s `ALLOC_SITES` (`:196`) resolved to the consumer's
  call-site return addresses (`alloc_call_sites`, `:250-298`;
  `alloc_ranges`, `:342-362`); the mirror declares it as an `AllocSite`
  (`Defs.lean:736-768`) and consumes it with `hiddenAlloc` (`:2202`).
- The arm record, kind 303, is written by `kcov_timer_arm` from
  `mod_timer` only (`gen:1194-1200`), for a timer function in the armed
  dispatch set; the queue record, kind 307, by `kcov_work_queued` from
  `__queue_work` (`gen:757-758`, `:830-852`), for a work function in the
  set; sections open in `process_one_work` and `call_timer_fn` for armed
  functions (`gen:748-751`, `:1183-1189`), the unit being the work or the
  timer address. The set is `harness/linux.py`'s `DISPATCH_SYMBOLS`
  (`:94-104`): fourteen of `DISPATCH_MAX` 16.
- The resched record, kind 302, is written only when `__cond_resched` is
  about to schedule and only inside a task's dispatch section
  (`gen:586-600`).
- The guest resets the remote area at every operation's start except
  before `wg_observe` (`harness/guest.c:2174`, `:2269`) and reads it at
  the operation's end (`:2674`), after that operation's wait. The
  end-of-wait jiffies read (kind 310) is taken after `wg_inject`'s,
  `wg_set`'s, `wg_up`'s, `wg_xmit`'s, `wg_batch`'s and `wg_advance`'s
  waits and before `wg_observe` (`:2608-2613`, `:2636`).

## 2. Question 1: under-load as a recorded input

### 2.1 The mirror today

`receiveHandshakePacket` (`Leanux/WG/Receive.lean:260-300`) computes
`under_load` from `Device.handshakeQueueLen` and declares the compare with
its operands (`branchCmp .hsUnderLoad`, the counter against 512; the
receive audit's F9 fix), saves the recorded clock (site 130) into
`World.lastUnderLoad`, and takes the decay from the recorded age test
(site 6) with `.hsDecayExpired`'s operands. The producer's increment is
`handshakeQueueLen + 1` at the ring produce; the worker's decrement is in
`receiveStep` (`:242`).

`Env.flood` (`Leanux/Env.lean:776-850`) builds the batch as the guest
does: the leading valids in the ring, the counter at the batch's size
(the measured fact that io_uring queues the whole batch before the
single-CPU worker runs). Then:

- the producer side of every send (520 `net_rx_action` sections, their
  IP-layer cut draws, the first packet's queue record) is dropped by
  `discardFloodRecords` (`Defs.lean:2236-2248`), which fails closed on
  any site outside its allow list;
- the leading valids run through `handshakeReceiveWorker` with their
  records;
- the invalid tail is folded by `floodTailEffect` (`:2264-2287`): per
  tail packet one `under_load_now` read at or over the threshold, or one
  decay read below it with the reset applied, and the resched records,
  into `lastUnderLoad`; the counter is set to 0 at the end; any other
  record is a mismatch;
- `LEANUX_FLOOD_EXACT=1` (`Main.lean:21`, `World.floodExact`) instead
  rebuilds the guest's 148-byte template (type 1, a MAC1 of `0xff`) and
  runs the tail through the real worker, for checking the summary against
  the unsummarised execution (the pre-release review's section 8).

The check's `control_flow` special-cases the operation (`evaluator/check.py:1043-1057`):
it requires `receive.c:115` covered iff the batch is at least 512 and
skips every decision of the operation; the batch size is read from the
trace, not from the records.

### 2.2 What a record of the counter at `:112` would add: nothing

The plan's row says "under-load as a recorded input at its kernel
source". Read literally, that is a new record kind carrying the
`atomic_read` at `:112`. It is not warranted, for three reasons verified
above:

- **The value is already recorded.** `:112-113` is a declared comparison;
  the comparison child records its operands at every execution, and the
  guest deduplicates rows by `(kind, operands, PC)` (`check.py:1233-1236`),
  so a tail of 520 packets whose counter runs 520, 519, …, 1 yields 520
  distinct rows, each of which a mirror `branchCmp` must match
  (`operand_rows_distinct`, `:1253-1256`). The instrument that would
  check the counter per packet exists; the mirror does not report the
  decisions it would be checked against.
- **The counter is not a hidden input.** It is kernel state computed by
  the producer's increments and the worker's decrements. Its hidden input
  is the producer/worker interleaving, which the NET_RX sections, the
  worker's section, the queue record and the resched records carry. A
  record of the counter would be an instrument on a derived value: the
  mirror would check it, never consume it. (The kind-311 caller read is a
  different case: `jiffies` is a genuine hidden input, the tick's.)
- **Every tail packet is already placed in the stream.** A packet at or
  over the threshold records the clock at `:115`; one below it with a
  saved `last_under_load` records the age test at `:117`. The only
  unplaced packet would be one below the threshold with `last_under_load
  == 0`, which inside one flood means a second of decay elapsed
  mid-drain: the drain takes about a millisecond (`docs/2026-10-05-e-dos.md`
  4.1, M4). It cannot happen in a flood that crossed; in one that did not
  (`e_underload_511`), no packet records anything and none needs to, the
  threshold's operands being the evidence.

**[AGENT] No new record kind for the counter.** The review's "a source
record if exact queue depth is otherwise ambiguous" is met by the exact
execution, which makes the depth unambiguous because the mirror computes
it from the same events the kernel does and the comparison instrument
checks it at every packet.

### 2.3 The change: retire the summary and the special case

The mirror runs the flood as what it is: a `wg_batch` of `count` sends of
the fixture's template, preceded by the leading valids and the optional
control, in the guest's order (`guest.c:1590-1594`). `Env.batch` (W7
stream B, `Leanux/Env/Batch.lean`) already runs an io_uring submission
exactly: each send's `net_rx_action` section is the producer
(`wg_packet_receive`: the handshake switch, the ring produce, the counter,
`queue_work_on` with its queue record for the first packet and the
pending bit for the rest), the receive worker's activation is resumed
where the resched records put it, and a worker that outlives the wait
fails closed. So:

- `Env.flood` becomes a thin wrapper: the template is an environment fact
  (the fixture's packet bytes, `Env.lean`, as `floodExact` builds it
  today), the items are the leading valids, the control if any, then
  `count` templates; the rest is `Env.batch`'s machinery with the
  handshake producer arm. `floodTailEffect`, `discardFloodRecords`,
  `World.floodExact` and `LEANUX_FLOOD_EXACT` are deleted.
- `handshakeQueueLen` is no longer set to the batch's size by the
  operation: it is incremented per produce and decremented per consume,
  and the batch-before-worker fact becomes what the records show, not an
  assumption. If a run ever had the worker preempt the submitter (it
  cannot on `PREEMPT_NONE` without a schedule point in the submission,
  and `io_uring_enter` has none, measured in the E design), the exact
  execution would follow the records anyway.
- The check's `wg_flood` arm in `control_flow` is deleted; the flood's
  decisions are checked like any operation's. The coverage rule on `:115`
  becomes the ordinary outcome check of `.hsUnderLoad`. The placement
  ceiling (`protocol.py:79`) already counts the flood's packets.
- The merged-injection control (`corpus/underload-controls/e_underload_merged`,
  `scripts/steering-controls.py:37,79`) loses its object: there is no
  discarded region for the control to land in. It becomes a positive trace
  (`e_underload_control_valid`: a mid-batch valid initiation gets its
  cookie reply like any other) and the control suite gets a replacement
  that exercises the new fail-closed edge: `e_underload_miscounted`, a
  flood whose trace says `count: 519` for a guest batch of 520 (the guest
  takes the count from the trace, so the control is built by the script
  with a deliberately mismatched mirror input), which leaves one producer
  section and one clock record unconsumed.

What stays environment: the template's bytes, the submission's order and
the guest's wait after the submission (`QUEUE_WAIT_US`, 100 ms, inside
the operation). Nothing moves into the mirror that is not the C's: the
producer and the worker are the mirror's already.

### 2.4 The measurement: exact versus summarised on s4

`e_underload_live` (520 invalid packets, no leading valid, then an
injection inside the decay), one run each way, the same guest build
(`check.py --suite wireguard --trace e_underload_live`, the second with
`LEANUX_FLOOD_EXACT=1 --no-build`); the flood is operation 3.

| | summarised | exact |
| --- | --- | --- |
| verdict | agreement, 7 operations | agreement, 7 operations |
| remote records of the flood operation (pc child) | 1,565: 520 clock reads (`:115`), 521 section starts and 521 stops (520 producers, one worker), 2 resched, 1 queue | 1,565, the same |
| mirror branches reported for the flood | 1 | 5,703 |
| operand pairs matched / distinct rows (trace) | 18 / 14 | 1,049 / 536 |
| the mirror on the recorded inputs (the trace, `scripts/in-bundle .lake/build/bin/leanux-model`) | 0.09 s | 0.10 s |

`e_underload_ratelimit` exact (two leading valids, one of them a cookie
reply and a steered MAC2 initiation): agreement, 5,885 branches for the
flood, 1,061 pairs over 544 rows, 0.10 s against 0.09 s.

The operand figures are the point: `operand_agreement` is not skipped
for the flood (only `control_flow` is), so in the exact run every tail
packet's `hsUnderLoad` compare was matched against Linux's rows, 520
distinct counter values, and all agreed. The counter is already checked
per packet by the instruments that exist; the summary only declines to
report it.

The record cost is the same: the tail already writes one clock record per
packet and the producers already open a section each; the summary
discards or folds what the exact execution consumes. The mirror's time
per packet, a MAC1 (`blake2s` over 116 bytes, `Leanux/WG/Blake2s.lean:68`,
a `List UInt8` implementation) and about a dozen decisions, is about
20 µs on this box: 10 ms for a flood of 520, and about 0.3 s for the
largest flood the harness accepts (`2^20` is the validator's ceiling,
`harness/trace.py:444`; a realistic maximum is the 16,384 of the E
measurements). At the corpus's flood sizes (510 to 520 invalid packets in
fourteen traces, `corpus/wireguard/e_underload_*`,
`l_delete_ratelimited`) the cost is nothing. The report bound is `MAX_BRANCHES = 262144`
(`protocol.py:230`); a 520-packet flood reports about 8,000 labels
(producer and worker arms per packet), and the W7 tier's 1,024-item batch
reports 126,531, so a flood of a few thousand packets is inside the bound
and a 16,384-packet one (the harness allows `2^20`) is not: the bound
becomes the flood's size limit, declared in the trace validator.

[AGENT] The exact execution is affordable at every size the corpus uses
and at the sizes the review asked for (a few thousand, to place the
boundary tightly); it replaces the summary. Nothing of the summary is
kept.

### 2.5 The busy test and the trylock (`:554-558`)

The producer's other read of the counter, `> MAX/2` for the trylock path,
is `.rxQueueBusy` (`Decision.lean:1147`), reached as true by any flood
over 1,024 packets and stopping as unsupported because `spin_trylock_bh`'s
outcome "is the worker's lock state at that instant, which no record
carries" (the receive audit). With the exact execution the producer's
section order relative to the worker's is recorded, but the lock is held
by `ptr_ring_consume_bh` only inside the worker's consume, so a producer
section that interleaves a worker activation at a resched record sees the
lock free (the worker yields between packets, `:216`, outside the
consume), and the trylock succeeds. On this single CPU the trylock can
fail only if the producer's softirq preempts the worker inside its
consume, which `ptr_ring_consume_bh` prevents (`_bh`: softirqs off). So
the outcome is derivable: success, always, on this config; the arm
`.rxQueueBusy` true then produces under the trylock exactly as the plain
path does. [AGENT] B4 declares it so, with the argument, and a trace
`e_underload_busy` (a flood of 1,100) covers the arm; `rxProduceFailed`
under the trylock (the ring full at 4,096) stays out of reach by the
flood size limit above.

### 2.6 Decisions and operands

No new decision on the under-load path. The decisions that become checked
per packet: `hsUnderLoad` (520 distinct operand rows per flood),
`hsWasUnderLoad`, `hsDecayExpired`, `hsCookie`, the `packet_needs_cookie`
arms, the MAC1 outcome (`cookieValidatePacket`'s decisions), and on the
producer side `wg_packet_receive`'s handshake arm, `.rxQueueBusy`, the
produce and the queue. The comparison child's area holds the 520 rows (a
`wg_create` window already exceeds that count by far).

## 3. Question 2: the GC as a dispatched unit

### 3.1 Today: it runs, unobserved

`gcEntries` (`Leanux/WG/Device.lean:131-161`) models the uninit walk
(`work = false`) and stops at `.gcHasWork` for a periodic run. The work
function is not in `DISPATCH_SYMBOLS`, so no section opens, the clock
read at `:57` is written in no recording context, and the requeue's
`add_timer_global` bypasses the arm hook even for an armed function. The
run is invisible.

It happens in every WireGuard trace. The timer is armed at `wg_create`
for `jiffies + 250` and re-armed by each run for `+ 250`. Measured on
`e_underload_live` (section 2.4's run): the end-of-wait reads give
`4294892911` after `wg_set`, `4294893291` after the last injection: 380
ticks, 1.52 s, from an instant already after the device's creation (the
cmp child: 523 ticks); `timing.jsonl` says 1.49 s and 2.03 s since
`wg_up`. So at least one GC run, and in the cmp child two, with the
tables empty: a walk of 2,048 buckets, a requeue, nothing else. A run
with entries matters: an entry idle for more than a second is freed, and
the next handshake from that source inserts (site 133) where the mirror,
holding the entry, predicts a hit (site 132). That is a hidden mismatch,
fail-closed, which is why the ratelimiter traces keep their second
initiation within the same tick and no trace advances past a second with
an entry in the table. The exclusion is safe; it bounds the corpus.

### 3.2 The representation at the thin layer

The GC is the C's data and control flow in the mirror (`gcEntries`,
completed), and three environment facts: when its timer fires, when the
kworker runs the work, and when the walk yields. All three come from
records.

- **State.** `Kernel.ratelimiter` gains `gcTimer : Option UInt64` (the
  pending timer's `expires`; `none` when not pending) and `gcPending :
  Bool` (the work's `WORK_STRUCT_PENDING_BIT`: set from the queue call
  until `process_one_work` starts the run). The refcount, the key and the
  two tables are as today.
- **Arming** (`:191` at init, `:81` at the requeue). `queue_delayed_work`
  is: if `gcPending` then nothing (the C's `test_and_set_bit`, a decision
  in `kernel/workqueue.c`, unanchored, so a plain `if` in the mirror);
  else `gcPending := true`, and the arm record (section 3.3) gives
  `{jiffies, expires, timer}`: the mirror checks `expires = jiffies + 250`
  (the C's `:2549`; `HZ` is a constant of the configuration) and records
  the timer's address as the unit (`timerUnits`, as `armTimer` does,
  `Leanux/WG/State.lean:145-160`). The init's arm happens inside
  `wg_create`'s own task context: a recording context, so the record is
  there.
- **Firing.** A section of `wg_ratelimiter_gc_entries` whose unit is the
  timer's address (section 3.3's hook) is the firing: the mirror requires
  `gcTimer` pending with `time_before(expires, J)` for a `J` it knows (the
  requeue's arm record inside the run that follows, or the end-of-wait
  read: section 3.5), clears `gcTimer`, and consumes the queue record
  (kind 307, the work's address) that `delayed_work_timer_fn`'s
  `__queue_work` writes inside the section; `gcPending` stays set (the
  bit was set at the arm). The section contains nothing else.
- **The run.** A section of the same function whose unit is the work's
  address: `gcPending := false` (`process_one_work` clears the bit
  before the call), then `gcEntries true`: the clock read (site 124),
  the walk over 2,048 buckets with, per bucket, the v4 and v6 entries
  whose expiry test `now - last_time_ns > NSEC_PER_SEC` is a new
  comparison decision each (`gcV4EntryExpired` at `:66`, `gcV6EntryExpired`
  at `:72`, operands `(now - last_time_ns, 1000000000)`), the entry's
  removal (`entry_uninit`: out of the table; the counter's decrement is
  deferred to the RCU callback, `:45`, so between the removal and the
  grace period the kernel's `total_entries` is higher than the mirror's
  table size: unobservable, the limit being out of reach, and declared
  with `rlOverLimit`'s reason), then `cond_resched` per bucket
  (`nestedResched` on the GC's worker: a resched record is consumed if
  one is there, as the receive worker's loop does), then the requeue (the
  arm above). The bucket a given entry lives in is a cut (the hsiphash),
  so the per-entry decisions are reported for bucket 0 standing for the
  walk, as today, and the `gcBucketIter` outcomes as a set.
- **Cancel** (`:211` at the last uninit). With the timer pending: it is
  deleted (`gcTimer := none`, `gcPending := false`; no record: the C's
  `try_to_grab_pending` is deterministic on the mirror's state). With the
  work queued and not started: the item is taken off the queue (the same
  fields). With the run in progress (the GC's activation suspended at a
  resched record): `cancel_delayed_work_sync` waits, so the mirror runs
  the activation to its section stop before the uninit proceeds (the W7
  activation machinery, `Env.schedule`), and the requeue inside that run
  arms a timer that the cancel then deletes. Then the uninit walk with
  `work = false`, as today, but over **both** tables (section 3.6).

### 3.3 The oracle changes: record-only, class-approved

Two existing LEANUX hook lines change and one gains a call; no kernel
source line is added or moved, and both files are unanchored (the checker
reads no spans from `kernel/time/timer.c` or `kernel/workqueue.c`).

1. **The firing section is named after the delayed work's function.** In
   `call_timer_fn` the hook (`gen:1187-1188`) becomes
   `kcov_dispatch_start(&section, fn == delayed_work_timer_fn ?
   (void *)container_of(timer, struct delayed_work, timer)->work.func : fn,
   timer);`. A delayed work whose function is armed opens a section named
   by that function with the timer as its unit; every other delayed work
   (vmstat, neighbour GC, and the rest) still opens none, since
   `delayed_work_timer_fn` itself is not armed. The queue record that
   `__queue_work` writes from inside is then in a recording context.
2. **The arm record at `__queue_delayed_work`.** The line
   `add_timer_global(timer);` (`workqueue.c:2561`) becomes
   `{ kcov_timer_arm(dwork->work.func, jiffies, timer->expires, _RET_IP_,
   timer); add_timer_global(timer); }`, and the two `add_timer_on` lines
   (`:2557`, `:2563`) the same (unreachable on this config, kept for the
   hook's honesty). Keyed on the work function, so only armed delayed
   works record, in the same format as `mod_timer`'s record. The requeue's
   caller frame is `ratelimiter.c:81`; the init's `ratelimiter.c:191`:
   two sites of kind 303 beside the peers' arm site.
3. `DISPATCH_SYMBOLS` gains `wg_ratelimiter_gc_entries` (harness, not
   kernel; the fifteenth of sixteen slots), armed by every WireGuard
   trace like the peer timers; `Worker.ratelimiterGc` in the mirror with
   its section site, `resched?` and the symbol, in the order the comment at
   `Defs.lean:950-956` prescribes.

The new identity and patch hash go in the merge's record. A behaviour
change there is none: no config option, no boot parameter, no functional
patch.

### 3.4 The harness: the inter-operation gap

The remote area is reset at each operation's start (`guest.c:2269`,
except before `wg_observe`) and read at its end (`:2674`), after that
operation's wait. A section that opens after the read and before the next
reset is lost, silently. No peer timer lands there: their delays (5 s and
up) exceed the trace bound, and the advance's wait is inside its
operation. The GC fires at every 250th tick wherever the guest is, so its
sections would land in the gap in a good fraction of runs, and the mirror
could not be exact: the arm record of a run in the gap is lost with it,
and the next run's section would name a unit never armed.

The fix is in the guest, one rule: **the remote area is never reset
between operations; each operation's remote row is the records since the
previous operation's read.** The read position moves instead of the
count. Records in the gap belong to the next operation as its head; the
mirror treats every operation's start as an idle point (the rule
`wg_observe` already has: "the guest's wait before this operation",
`Env.observe`, `Env.lean:688`), consuming the GC's firing and run there
before the operation's own records. The per-operation rows the checker
builds (`check.py:555-595`) do not change shape. This closes an instrument
gap that exists today for every armed unit, not only the GC; the trace
bound made it unreachable, which is a bound, not a rule. One-off mutant: a
guest that keeps the reset, run on a trace whose GC fires in a gap (an
advance of 300 ticks between two operations with no wait of their own):
the mirror finds the run's section missing and the next arm's unit unknown
(rejected).

### 3.5 The environment rule, new

> **The ratelimiter GC's two units (the firing, the run) are dispatched
> wherever the records place them, never predicted.** (i) At an
> operation's start (the gap before it) and at an idle point inside an
> operation (`idleTimers`, `afterAdvance`): consumed by `runTimers`'s loop
> like a peer timer's section, the firing's due test against the
> end-of-wait read where one exists. (ii) Inside a task section at a record
> boundary (the tick landed in the trace task's own system call or in a
> kworker's section): the firing is a softirq section nested there, read by
> `hidden` as an ambient dispatched unit at that point; the run's section
> follows at the task's next yield, which for a kworker is a resched record
> (the activation machinery) and for the trace task is its return to user
> mode, i.e. the operation's end or the gap. (iii) Never inside a softirq
> section (the timer and NET_RX vectors are siblings, `handle_softirqs`).
> The firing's due test when no end-of-wait read bounds it is the requeue's
> own arm record inside the run that follows: `time_before(expires,
> jiffies_at_requeue)` is the kernel's `__run_timers` invariant and is
> exact. A GC section with no pending GC timer, a run with `gcPending`
> clear, or a requeue whose jiffies is not past the fired expiry is a hidden
> mismatch.

Case (ii) is the rule the mirror lacks. `skipAmbient` (`Defs.lean:2180`)
drops ambient *records*; a nested ambient *section* with content (the
queue record) needs `hidden` to recognise the GC's section start, run the
firing, and continue with the record it was asked for. That is a small,
general mechanism ("an ambient dispatched unit at any read"), and it is
the stream's stop risk (section 11): if it cannot be made exact and
fail-closed, the GC cannot be a dispatched unit on this fixture, and the
exclusion stays with its reason sharpened.

Whether an environment rule moves into the mirror: no. The GC's walk,
removal and requeue are the mirror's (the C's); the placement of its
sections is the environment's, from records.

### 3.6 Does any corpus trace reach a run today; what exercises it

Every WireGuard trace longer than a second after `wg_create` reaches one
or more runs, unobserved (section 3.1). With B4 every such trace gains
the GC's sections in its records and the mirror consumes them; the traces
themselves do not change. The runs with entries, which is what the GC is
for, need new traces:

| Trace | Content | What it checks |
| --- | --- | --- |
| `e_underload_ratelimit_gc` | flood; an initiation from one source inserts; `wg_advance` 300; the GC's run frees the entry (`gcV4EntryExpired` true, operands); the same source inserts again (site 133 twice, no 132) | the periodic walk with an entry, the expiry comparison, the arm and firing records |
| `e_underload_ratelimit_gc_kept` | as above with `wg_advance` 200 then the second initiation inside the entry's second: the run keeps it (`gcV4EntryExpired` false), the second initiation hits (site 132) | the comparison's false arm |
| `e_underload_ratelimit6_gc` | the v6 table's run with an entry (`gcV6EntryExpired`) | the second table's walk |
| `l_delete_ratelimited6` | an IPv6 entry, then `wg_delete`: the uninit walk over the v6 table | the uninit's v6 arm, today constant false |
| `l_recreate_ratelimited6` | as above, then `wg_create`, `wg_set`, `wg_up` and an initiation from the same `/64`: an insert (the kernel emptied the table at uninit) | the mirror defect below, as a positive trace once fixed |
| `e_underload_busy` | a flood of 1,100 | `.rxQueueBusy` true under the trylock (section 2.5) |

**A mirror defect, found reading (Rule Zero, clause 1).** `gcEntries`
with `work = false` empties `table` and reports `gcV6EntryIter` false
always (`Device.lean:150-155`), and `ratelimiterInit` resets `table`
only (`:128`): after a delete with IPv6 entries and a re-create, the
mirror holds entries the kernel freed (`:70-74` on the uninit walk). The
next IPv6 initiation from that `/64` would be a hit in the mirror (site
132) and an insert in the kernel (site 133): a hidden mismatch, so the
verdict today could not be wrong silently; no trace does this, so the
defect has been invisible. The comment on `gcEntries` ("the entries are
IPv4") predates F12. B4 fixes both (`gcEntries` walks both tables;
`ratelimiterInit` resets both; the comment), with `l_recreate_ratelimited6`
as the witness. The `WGCookie.lean` frame of campaign 1 already views both
tables (`Framing/WGCookie.lean:19`), so the frame is right and the mirror
was behind it.

### 3.7 The interface requirement on the timer representation (B3)

Written against the interface, not B3's note (not read). Whichever
representation lands, the GC needs:

- **R1, an owner beside the peers.** A kernel-global timer
  (`Kernel.ratelimiter.gcTimer`) with `expires`, pending or not, armed
  and deleted by the ratelimiter's code, not a peer's.
- **R2, the arm.** The same consumption shape as `armTimer`'s: a kind-303
  record `{jiffies, expires, timer}` at the arm site, the caller's delay
  checked against the published expiry (`expires = jiffies + HZ`; the
  caller's own read is the same instant here, `:2549`, so no kind-311
  record is needed), the timer's address registered as the unit.
- **R3, the firing.** A record-placed section whose due test is
  `time_before(expires, J)` for a `J` the mirror knows, or, under a wheel
  representation, the wheel's own order among the timers due at the
  tick. The GC timer is `TIMER_DEFERRABLE | TIMER_IRQSAFE` in the one
  base of this configuration (section 1.3); if B3 models bucket
  placement, the deferrable flag must be stated as not changing it here.
- **R4, deletion** at `cancel_delayed_work_sync`, from the mirror's
  state, no record.
- **R5, nesting.** The firing may land inside a task section (section
  3.5, case ii); the peer timers do not need this, the GC does.
- **R6, the pairing.** The timer unit is armed by the 303 record and
  consumed by the firing section; the work unit by the 307 record inside
  that section and the run's section (`dispatch_problems`,
  `check.py:748-798`, unchanged).

If B3 lands first, the GC timer joins the wheel as one more `timer_list`;
if B4 lands first, R1-R6 are met by the record-driven firing and B3
replaces R3's due test by the wheel. Neither blocks the other.

## 4. Question 3: the entry allocation

### 4.1 The C

`kmem_cache_alloc(entry_cache, GFP_KERNEL)` at `:138`, in the handshake
receive worker (process context, a kworker). On NULL: `err_oom` (`:153`)
decrements `total_entries` and returns false, so
`wg_cookie_validate_packet` returns `VALID_MAC_WITH_COOKIE_BUT_RATELIMITED`
(`cookie.c:146-148`), which `packet_needs_cookie`'s table drops
(`receive.c:129-132`): the initiation is not consumed and no response is
sent. Observable.

### 4.2 The mirror today, and a wrong sentence

`ratelimiterAllow` (`Receive.lean:192-197`): `branch .rlAllocFail
!(← envOk .ratelimiterEntry)` and the arm `unsupported`. `envOk` is the
pipes-era environment oracle (`EnvSite`, `Defs.lean:697-709`), which
always answers success. The E design's section 11 says the site "is not in
the kind-305 hook's list (`kernel/patches/gen-choice-stream.py`)". There
is no such list: the hook is generic (section 1.4) and records any armed
range; what is missing is the site's row in `ALLOC_SITES` and its
`AllocSite` constructor. B4 corrects the sentence in the E design and the
receive audit's F13 row.

### 4.3 The change: no kernel change

- `AllocSite.kmemCacheAllocRlEntry`: consumer `drivers/net/wireguard/ratelimiter.c:138`,
  a direct site (`kmem_cache_alloc_noprof` is in `ALLOC_ENTRIES`,
  `steer.py:161`; the return address is in `wg_ratelimiter_allow`),
  `.exact 1`, hidden id `70 + index`; the `ALLOC_SITES` row with
  `cls='kworker'`, like `kzallocKeypair` (`noise.c:100`, `steer.py:219`):
  the receive worker's context.
- `ratelimiterAllow` consumes it with `hiddenAlloc`; the false arm is the
  C's `err_oom`: the counter back by one and `return false`, so
  `cookieValidatePacket` returns `.ratelimited` and the packet is
  dropped. The arm is modelled, not `unsupported`. `EnvSite.ratelimiterEntry`
  is deleted.
- Arming. A chunk is armed for a site when a trace steers it or the run's
  `arm` lists it (`check.py:1568-1578`); `hiddenAlloc` answers success
  unarmed (the A design's transitional rule, 6.6, still in force:
  `Defs.lean:2220`). The ratelimiter traces (`e_underload_ratelimit*`,
  `l_delete_ratelimited`, the GC traces above) declare the site with a
  `draw` entry so their chunk records it and the mirror consumes the
  record; the success outcome is then checked, not assumed.
- The failure arm is reachable only by steering, and the `kworker` class
  is not steerable (`ENABLED_CLASSES = {'atomic'}`, the `failslab`
  extension adds `task`; `steer.py:180-181`): the user's A1 decision. B4
  does not propose a `kworker` class; the arm stays declared and
  unreached, named in the census as such, like `kzallocKeypair`'s.
- One-off instrument mutant: the mirror keeps `envOk` (consumes no
  record) while the chunk is armed: the record is left unconsumed ("a
  record of site N was not consumed", `Runner.lean:1056-1057`): rejected.
  Deleted after its run.

### 4.4 The init's allocations stay outside the model

`KMEM_CACHE(ratelimiter_entry, 0)` (`:164`) and the two `kvcalloc(2048,
8, GFP_KERNEL)` (`:179`, `:184`) are not direct sites. The cache
creation allocates several objects through `mm/slab_common.c` (the cache,
its name, the per-CPU slabs, its sysfs and debugfs entries) with a
state-dependent count; a 16 KiB `kvcalloc` exceeds
`KMALLOC_MAX_CACHE_SIZE` and goes to `kmalloc_large` and the page hook
from `mm/slub.c` addresses, which are never armed (A design 4.1), with a
`vmalloc` fallback that the A design declares never failed (6.2, M7).
These are the creation allocations the A design keeps lax or cut (2.5).
[AGENT] Census row 132 stands. The three `envOk` branches
(`.ratelimiterInitCacheErr`, `TableV4Err`, `TableV6Err`) become
constant-false decisions with this reason, as `dstCacheInit`'s did (A
design 6.4), and `EnvSite.ratelimiterCache` and `.ratelimiterTable` are
deleted with them. `EnvSite` keeps its pipe-path sites.

## 5. Records: derived and new

| Record | Today | After B4 |
| --- | --- | --- |
| the clock per tail packet (`:115`, site 130) | folded by `floodTailEffect` | consumed by the worker per packet |
| the decay read in a tail (`:117`, site 6) | folded | consumed per packet |
| the producer sections and the IP-layer draws of a flood | discarded by `discardFloodRecords` | consumed by the producer per packet (`Env.batch`) |
| the flood's queue and resched records | dropped | consumed (the first packet's queue, the worker's yields) |
| the counter at `:112` | derived; its compare's operands recorded and unchecked for the tail | derived; checked per packet |
| the GC's clock (`:57`, site 124) | never in a recording context | consumed per run |
| the GC's firing and run sections (kind 300/301) | none | new, from the dispatch set |
| the GC's queue record (kind 307) | none | new, inside the firing section |
| the GC's arm records (`:191`, `:81`, kind 303) | none | new, from the `__queue_delayed_work` hook |
| the GC's resched records (`:78`) | none | consumed when present |
| the entry allocation (`:138`, kind 305) | `envOk` | a declared site, consumed when the chunk is armed |

All new records are record-only. No behaviour change is proposed; the
only candidate that would be one, arming `delayed_work_timer_fn` itself,
is rejected in section 3.3 because it would section every delayed work.

## 6. Environment rules touched

- `Env.flood`: rewritten over `Env.batch`; the summary, the discard and
  the exact flag deleted (section 2.3).
- The decay: unchanged in the mirror (`receiveHandshakePacket`); the
  environment no longer folds it.
- A new rule for the GC's placement (section 3.5), including the ambient
  nested section at any read.
- Every operation's start is an idle point (section 3.4), which is the
  `wg_observe` rule generalised.
- `requireDrained` at the flood's end: the worker drained within the wait
  or the operation fails, as `wg_batch` has it.

## 7. Decisions and operands added

| Decision | Site | Operands | Note |
| --- | --- | --- | --- |
| `gcV4EntryExpired` | `ratelimiter.c:66` | `now - last_time_ns` vs `NSEC_PER_SEC` | `gt`, non-constant rhs is a constant: `const_rhs` |
| `gcV6EntryExpired` | `ratelimiter.c:72` | the same | |
| `.rxQueueBusy` true arm | `receive.c:554-558` | none new | the trylock's success derived (section 2.5) |
| `.ratelimiterInit{Cache,TableV4,TableV6}Err` | `:165`, `:180`, `:185` | none | constant false with the reason |
| `.rlAllocFail` | `:139` | none | over the record; the true arm modelled |

No decision is removed. The flood's existing decisions become checked.

## 8. One-off mutants

| Mutant | Rejected by |
| --- | --- |
| the mirror ignores the resched records of the flood's worker (runs it in one activation) | the W7 interleaving: a producer section between activations is consumed in the wrong order, hidden mismatch |
| the arm hook keyed on the timer's function instead of the work's (no record) | `ratelimiterInit` finds no arm record |
| the firing section named `delayed_work_timer_fn` (hook 1 reverted) | the section is from an unlisted function: the coverage boundary |
| the guest's per-operation reset kept (section 3.4) | a GC run in a gap: the next arm names an unknown unit |
| `envOk` kept for the entry while the chunk is armed | an unconsumed record |

Each run once in its commit and deleted; none replaces a sentinel. The
sentinel set does not change: `E-M8` (queue under-load ignored) is covered
by the exact execution's `hsUnderLoad` rows, and `E-M10/M11` by the
ratelimit traces as today.

## 9. Corpus

Additions: the six traces of section 3.6, `e_underload_control_valid`
(the former control as a positive trace), and the control
`e_underload_miscounted` replacing `e_underload_merged` in
`corpus/underload-controls` and `scripts/steering-controls.py`. Changes:
none to existing traces; every WireGuard trace's records gain the GC's
sections, which the mirror consumes. The suite's run time grows by the
exact flood execution (section 2.4) across fourteen traces.

## 10. Proof-tree frames touched

Read-only, by `git show` of both branches.

- `proofs/campaign`, `Leanux/Proofs/Framing/EnvOperations.lean:78`
  (`floodTailEffect_sameKernel`) and `Framing/Kernel.lean:247-252`
  (`discardFloodRecords_sameWGKernel`, `_spec`): their subjects are
  deleted; the frames go, and `Env.flood`'s frame is re-proved over
  `Env.batch`'s (which the campaign already frames for `wg_batch`).
- `proofs/campaign`, `Framing/WGCookie.lean:55-78`
  (`ratelimiterAllow_sameCookieKernel`): `hiddenAlloc` replaces `envOk`
  in the body; the view is unchanged (both tables are already in it,
  `:19`). A re-run.
- `proofs/campaign`, `Framing/WGDeviceLifecycle.lean:13-51`
  (`ratelimiterKernel`, `ratelimiterInit_`, `gcEntries_`,
  `ratelimiterUninit_sameRatelimiterKernel`): the view erases
  `ratelimiter` wholesale (`:13`), so `gcTimer`/`gcPending` and the
  two-table walk are inside the erased field: the statements hold, the
  proofs re-run with the new arms (`gcEntries true` no longer stops).
- `proofs/campaign-2`, `Leanux/Proofs/Logged/Operations.lean:255-303`
  (`floodLogged`, `floodLogged_erases`) and `Logged/Syscalls.lean:30,49`:
  a line-by-line copy of `Env.flood` with an erasure proof; it must be
  re-mirrored over the new `Env.flood`. A lag-and-repair item for the
  campaign, per the register rule; the integration record says so.
- Campaign 2's H2 (index uniqueness) and H5 (termination under fairness)
  are not over the ratelimiter or the flood; H6 (timer discipline) may
  take the GC timer as a non-peer timer into its model or exclude it by
  name, which the charter leaves to the campaign.

## 11. Risks

1. **The nested GC section (the stop risk).** Case (ii) of section 3.5
   needs `hidden` to accept an ambient dispatched unit at any read inside
   a task section, exactly and fail-closed. Today the mirror has
   `skipAmbient` for records and the NET_RX `sectionOf` machinery for
   loopback transmissions; a timer section with content nested at an
   arbitrary point is new. If it cannot be made exact (a GC firing inside
   a kworker's section whose work section then interleaves that
   kworker's remaining activations in an order the resched records do
   not determine), B4 stops at the GC and lands questions 1 and 3 alone;
   the GC exclusion is then rewritten with this reason. Settled in the
   first day of the build on `e_underload_ratelimit_gc` under the W7
   activation machinery, before anything else of the GC is built.
2. **The gap rule changes every trace's remote rows.** The guest's
   per-operation reset is gone for all suites; FS traces have no remote
   area, seccomp traces none; the WireGuard suites re-record. If a unit
   other than the GC turns out to land in gaps today (none should by the
   bound), it surfaces as new mismatches at the claim point, which is the
   point.
3. **The exact flood's time.** Measured negligible (section 2.4: 10 ms
   for 520 packets, the model's whole trace in a tenth of a second); the
   cost that remains is the report's size, risk 4. Not a risk.
4. **The report bound.** A flood above a few thousand packets exceeds
   `MAX_BRANCHES`; the validator refuses it with the reason, which bounds
   the boundary traces the review asked for to a few thousand. Enough for
   511/512/513 and for 1,100.
5. **The dispatch set's last slot.** Fifteen of sixteen after B4; B2's
   second device needs no symbol (the NAPI and workers are per device by
   unit, not by function), but a sixteenth unit anywhere means raising
   `DISPATCH_MAX`, a record-only change.
6. **Campaign 2's `floodLogged` copy** lags until repaired; the register
   says so at the landing.

## 12. Estimate

About 0.15 WU (one WU being WireGuard's three weeks,
`docs/2026-10-12-kernel-scout.md`), three to four agent-days of build:

| Part | Days |
| --- | --- |
| the flood over `Env.batch`, the deletions, the check's arm, the control's replacement, the busy arm, the boundary and busy traces | 1.5 |
| the GC: the two hooks and the rebuild, the dispatch symbol, the state and the arms, the firing and the run, the gap rule in the guest and the mirror, the nested-section rule, four traces | 1 to 1.5 |
| the entry allocation site, the init's constant arms, the docs (E design 11, the receive audit's F13, the census rows 132-135, `docs/decisions.md`), the one-off mutants | 0.5 |

Plus the settling pass on s5 (the rebuilt oracle: the claim point's full
check, controls and sentinels) and the audit the plan schedules before the
build.

## 13. Decisions: the user's, and tactical

For the user:

- **U1.** The flood becomes a `wg_batch` in the mirror and the summary,
  the discard, the exact flag and the check's special case are deleted
  (section 2.3). The merged-injection control is replaced by the
  miscount control. This retires a declared summary contract from the
  trust surface in favour of the ordinary check.
- **U2.** The GC is made a dispatched unit with the two hook changes of
  section 3.3 (record-only, class-approved, but listed here because they
  touch the timer and workqueue hooks every other unit uses) and the
  guest's gap rule of section 3.4, which changes how every operation's
  remote row is cut.
- **U3.** The nested-section rule (section 3.5, case ii) as the stop
  condition: if it cannot be exact, the GC stays excluded and B4 lands
  without it.

Tactical [AGENT]:

- no record kind for the counter (section 2.2);
- the trylock's success derived on this config (section 2.5);
- the GC's per-entry comparisons as two decisions with operands;
- the entry site record-only, no `kworker` steering class (section 4.3);
- the init's three allocations constant-false with the reason, census
  row 132 unchanged (section 4.4);
- the two-table uninit fix and the comment, with `l_recreate_ratelimited6`
  as its witness (section 3.6);
- the flood size limit at the report bound (section 2.4).
