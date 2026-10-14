# B4 design: load as a recorded input, the ratelimiter's GC, the entry allocation — 2026-10-15

Stream B4 of [the parallel plan](2026-10-14-wireguard-parallel-plan.md)
(section 2, row B4). Design only; nothing here is built. Revised against
[the independent review](2026-10-15-design-b4-review.md) (cd183e0, 21
findings): every finding is dispositioned in section 14. The measurement
of section 2.4 was taken on the s4 oracle (identity `6b2018b9…`) before
the review; no run was made for the revision [AGENT, fork of the
coordinator].

## 0. Summary

Three questions; after the review, two are built now and one leaves the
stream.

1. **Under-load as a recorded input: no new record kind.** The kernel
   already records what the decision depends on: the compare's operands
   at `receive.c:112-113`, a clock read per packet at `:115` (site 130) or
   `:117` (site 6), and the producer and worker sections with the queue
   and resched records. The mirror does not use them for the flood's
   tail: it summarises the tail (`floodTailEffect`) and the checker skips
   the flood's decisions. The change is to run the flood as the
   `wg_batch` it is, delete the summary, the discard and the exact flag,
   and replace the checker's special case by a named rule change on the
   trust surface (section 2.3, U1). The measurement taken so far ran the
   exact flag's path, which keeps the discard and the preset counter and
   skips control flow; it is restated as exactly that (section 2.4), and
   the prototype of the real path over the thirteen flood traces and the
   control is the build's first step, with a stop condition.
2. **The GC: deferred to its own stream.** The review found three
   concrete defects in the GC design (the arm hook's attribution, the
   cancel model, the gap rule) and four missing rules. The exclusion
   stays, with its reason sharpened by the review's facts (section 3).
   The claim that the inter-operation gap is a silent instrument gap is
   retracted: `section_problems` fails a lost section loudly. U2 is
   withdrawn.
3. **The entry allocation: no kernel change.** The kind-305 hook is
   generic; the site is a row in `harness/steer.py`'s `ALLOC_SITES` plus
   an `AllocSite` constructor; the failure arm becomes the C's `err_oom`
   drop, modelled, reachable only by steering a class the host does not
   enable. The init's three allocations stay outside the model with the
   reason written (section 4).

With the GC out, B4 needs **no oracle change**: it lands on s4. The
two-table uninit defect (section 3.5) is fixed in the same build.

Estimate for questions 1 and 3 plus the uninit fix: about 2.25
agent-days, roughly 0.1 WU (section 12); the proof-tree repair it forces
is costed separately (section 10).

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

`last_under_load` is a function-local static (`:100`).
`MAX_QUEUED_INCOMING_HANDSHAKES` is 4096 (`messages.h:51`): the
under-load threshold is 512, the busy threshold 2,048. The producer
(`wg_packet_receive`, softirq) tests `handshake_queue_len > MAX/2` for the
trylock path (`:554-558`, `spin_trylock_bh` on `producer_lock`),
produces (`:560`, `ptr_ring_produce_bh`: `producer_lock`,
`ptr_ring.h:160-164`), increments (`:567`) and queues the worker
(`:570-571`). The worker (`:206-218`) consumes under `consumer_lock`
(`ptr_ring_consume_bh`, `ptr_ring.h:362-368`; `:212`), handles (`:213`),
decrements (`:215`) and `cond_resched`s (`:216`) per packet.

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

### 1.3 The delayed work and the configuration (kept for the GC stream)

`DECLARE_DEFERRABLE_WORK(gc_work, wg_ratelimiter_gc_entries)` (`:20`) is
a `delayed_work` whose timer has function `delayed_work_timer_fn` and
flags `TIMER_DEFERRABLE | TIMER_IRQSAFE` (`include/linux/workqueue.h:244-257`).
`queue_delayed_work` (`workqueue.h:676-682`) is `queue_delayed_work_on`
(`kernel/workqueue.c:2575-2595`): `test_and_set_bit(WORK_STRUCT_PENDING_BIT)`
and `!clear_pending_if_disabled(work)` (`:2585-2586`; the function at
`:2386-2399` clears the bit again, without queueing, when the work is
disabled), then `__queue_delayed_work` (`:2524-2562`): `delay == 0`
queues at once (`:2541-2544`), else `timer->expires = jiffies + delay`
(`:2548`) and, housekeeping disabled on this config, `add_timer_global`
(`:2558`; `add_timer_on` at `:2555` and `:2560`), which is
`__mod_timer(…, MOD_TIMER_NOTPENDING)` (`kernel/time/timer.c:1325-1331`)
and so **bypasses `mod_timer`**, where the kind-303 arm hook sits.
`__queue_delayed_work` is out of line in the oracle (`System.map`:
`ffffffff81090570 t __queue_delayed_work`). The timer's callback
`delayed_work_timer_fn` (`:2515-2521`) is `__queue_work(dwork->cpu,
dwork->wq, &dwork->work)`. `cancel_delayed_work_sync` (`:4470-4474`) is
`__cancel_work_sync(…, WORK_CANCEL_DELAYED)` (`:4382-4402`): it cancels
with `WORK_CANCEL_DISABLE` (`:4386`), flushes a running instance
(`:4397-4398`) and re-enables the work only afterwards (`:4400-4401`), so
**a requeue issued while the cancel waits sets PENDING and has it cleared
by `clear_pending_if_disabled`: nothing is armed**.

The wheel rounds an expiry up to its level's granularity
(`calc_index`, `timer.c:579-581`: `expires = (expires >> LVL_SHIFT(lvl))
+ 1`); with `LVL_CLK_SHIFT = 3` and `LVL_BITS = 6` (`:154`, `:168`), a
delay of 250 ticks lands on level 1 (`LVL_START(1) = 63`, granularity 8),
so the GC timer fires in `(E, E + 8]`.

The oracle's configuration (`kernel/config-x86_64-net-choice`): `HZ=250`,
`HZ_PERIODIC` (no `NO_HZ`: `NR_BASES = 1`, so `BASE_DEF` is the one base,
`timer.c:200-203`, and the deferrable flag changes nothing about
placement), `PREEMPT_NONE`, no `SMP`, no `DEBUG_SPINLOCK`, `IPV6`, no
`WQ_POWER_EFFICIENT_DEFAULT` (`system_power_efficient_wq` is an ordinary
per-CPU workqueue, `workqueue.c:7876-7877`), no `CPU_ISOLATION`.

### 1.4 The instruments as they stand

- Clock reads are wrapped generically (`kernel/patches/gen-choice-stream.py:444-457`):
  every exported reader records `{kind 200+, _RET_IP_, value}`, attributed
  to the caller's frame. So `:117`, `:57`, `:115`, `:121`, `:146` are
  sites 6, 124, 130, 132, 133 (`Leanux/Kernel/Defs.lean:1209`, `:1290`,
  `:1328`, `:1332`, `:1333`), written only in a recording context
  (`kcov_choice_write`: outside one, nothing, uncounted).
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
  (`:94-104`), armed per trace by `arm_masks` (`:106-127`): fourteen
  symbols; `Defs.lean:950-956` reserves indices 14-15 for W5-W6's units.
- The resched record, kind 302, is written only when `__cond_resched` is
  about to schedule and only inside a task's dispatch section
  (`gen:586-600`).
- The guest resets the remote area at every operation's start except
  before `wg_observe` (`harness/guest.c:2174`, `:2269`) and reads it at
  the operation's end (`:2674`), after that operation's wait; after the
  trace it reads the kernel's count of opened sections
  (`KCOV_LEANUX_SECTION_STATUS`, `:1480-1484`) and the checker's
  `section_problems` (`evaluator/check.py:653-667`) fails the trace when
  the recorded section starts do not match it. The end-of-wait jiffies
  read (kind 310) is taken after `wg_inject`'s, `wg_set`'s, `wg_up`'s,
  `wg_xmit`'s, `wg_batch`'s and `wg_advance`'s waits and before
  `wg_observe` (`:2608-2613`, `:2636`).

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

`Env.flood` (`Leanux/Env.lean:791-850`) builds the batch as the guest
does: the leading valids in the ring, the counter at the batch's size
(the measured fact that io_uring queues the whole batch before the
single-CPU worker runs). Then:

- the producer side of every send (520 `net_rx_action` sections, their
  IP-layer cut draws, the first packet's queue record) is dropped by
  `discardFloodRecords` (`:812`; `Defs.lean:2236-2248`), which fails
  closed on any site outside its allow list;
- the leading valids run through `handshakeReceiveWorker` with their
  records;
- the invalid tail is folded by `floodTailEffect` (`Defs.lean:2264-2287`):
  per tail packet one `under_load_now` read at or over the threshold, or
  one decay read below it with the reset applied, and the resched
  records, into `lastUnderLoad`; the counter is set to 0 at the end; any
  other record is a mismatch;
- `LEANUX_FLOOD_EXACT=1` (`Main.lean:21`, `World.floodExact`,
  `Defs.lean:1495`) takes a branch **after the discard** (`Env.lean:821`)
  that rebuilds the guest's 148-byte template (type 1, a MAC1 of `0xff`),
  **still presets the counter to the batch's size** (`:828`) and runs the
  tail through the real worker. It was built to check the summary's fold
  against the worker, not the producer side, and not the design below.

The checker's `control_flow` special-cases the operation
(`evaluator/check.py:1043-1059`): it requires `receive.c:115` covered iff
the batch is at least 512 and skips every decision of the operation; the
batch size is read from the trace, not from the records.

### 2.2 What a record of the counter at `:112` would add: nothing

The plan's row says "under-load as a recorded input at its kernel
source". Read literally, that is a new record kind carrying the
`atomic_read` at `:112`. It is not warranted, for three reasons verified
above:

- **The value is already recorded.** `:112-113` is a declared comparison
  whose operands the comparison child records at every execution; the
  guest deduplicates rows by `(kind, operands, PC)` (`check.py:1233-1236`),
  so a tail of 520 packets whose counter runs 520, 519, …, 1 yields 520
  distinct rows. The instrument is one-directional: each mirror
  obligation must match some kernel row, and surplus kernel rows need no
  counterpart (`:1241-1246`, the pre-release review's finding 5);
  `operand_rows_distinct` is a report counter (`:1857`, `:1908`), not a
  check. So the rows check what the mirror reports, never what it omits.
- **The counter is not a hidden input.** It is kernel state computed by
  the producer's increments and the worker's decrements. Its hidden input
  is the producer/worker interleaving, which the NET_RX sections, the
  worker's section, the queue record and the resched records carry. A
  record of the counter would be an instrument on a derived value: the
  mirror would check it, never consume it. (The kind-311 caller read is a
  different case: `jiffies` is a genuine hidden input, the tick's.)
- **Every tail packet is placed in the stream, in order, by its clock
  record.** A packet at or over the threshold records the clock at
  `:115`; one below it with a saved `last_under_load` records the age
  test at `:117`. Those records are consumed in order at their exact
  sites, and that consumption, not the operand rows, is what makes the
  exact execution per-packet complete. The only unplaced packet would be
  one below the threshold with `last_under_load == 0`, which inside one
  flood means a second of decay elapsed mid-drain: the drain takes about
  a millisecond (`docs/2026-10-05-e-dos.md` 4.1, M4). It cannot happen in
  a flood that crossed; in one that did not (`e_underload_511`), no
  packet records anything and none needs to, the threshold's operands
  being the evidence.

**[AGENT] No new record kind for the counter.** The review's "a source
record if exact queue depth is otherwise ambiguous" is met by the exact
execution, which computes the depth from the same events the kernel does,
with every packet's clock record consumed in order.

### 2.3 The change: the flood over `Env.batch`, and the checker rule it needs

The mirror runs the flood as what it is: a `wg_batch` of `count` sends of
the fixture's template, preceded by the leading valids and the optional
control, in the guest's order (`guest.c:1588-1594`). `Env.batch` (W7
stream B, `Env.lean:895`, `afterBatch` `:870`) already runs an io_uring
submission exactly: each send's `net_rx_action` section is the producer
(`wg_packet_receive`: the handshake switch, the ring produce, the counter,
`queue_work_on` with its queue record for the first packet and the
pending bit for the rest), the receive worker's activation is resumed
where the resched records put it, a section between two items' records
mismatches (`:887-893`: the sends run inline in the trace task and the
kworkers wait for the call to return), and a worker that outlives the
wait fails closed. So:

- `Env.flood` becomes a thin wrapper: the template is an environment fact
  (the fixture's packet bytes, as the exact branch builds it today), the
  items are the leading valids, the control if any, then `count`
  templates; the rest is `Env.batch`'s machinery with the handshake
  producer arm. `floodTailEffect`, `discardFloodRecords`,
  `World.floodExact`, the `LEANUX_FLOOD_EXACT` switch and
  `executeTrace`'s `floodExact` parameter are deleted.
- `handshakeQueueLen` is no longer set to the batch's size by the
  operation: it is incremented per produce and decremented per consume.
  The batch-before-worker fact is then what the records show; a worker
  section between two producers' records is a mismatch, as `Env.batch`
  has it, which is the right fail-closed behaviour.
- The flood's drain: `afterBatch`'s `requireDrained` (`:881-882`) lists
  the decrypt, encrypt, tx and send queues and not the handshake queue;
  the flood wrapper adds the handshake queue and the counter at zero, so
  a receive worker that outlives the wait stops the operation.
- **The checker rule change (U1).** Without the `wg_flood` arm the flood
  goes through the ordinary `control_flow` rules, and every flood would
  fail: "decision reported more than once" applies to every decision not
  declared `repeatable` and to every operation but `wg_batch` and
  `wg_netns_close` (`check.py:1095-1106`); "opposite outcome covered"
  applies unless the decision is `repeatable` (`:1133-1140`); and none of
  the flood path's decisions is repeatable (`Decision.repeatable`,
  `Leanux/Kernel/Decision.lean:2959-3065`: of the path only
  `workerConsumed` is). The flood also needs the batch's file restriction
  (`op_files = BATCH_FILES(...)` for `wg_batch`, `:1066`): its
  `io_uring_enter` runs the same fixture plumbing in `fs/file.c` that the
  batch excludes. The change, then, is three rules on the trust surface:
  `wg_flood` joins `wg_batch` in the file restriction and in the repeat
  rule's exemption, and the decisions a flood evaluates with both
  outcomes in one operation are declared `repeatable`: `hsUnderLoad`
  (true for the first 9 packets of 520, false after), `macInvalid` (the
  valids against the tail), the `packet_needs_cookie` arms that take both
  outcomes (`hsLoadedCookieOk`, `hsMacNoCookie`, `hsNeedsCookieMac`),
  `rxQueueBusy` (the busy trace), and, found by the prototype run, the
  consume path's `consumeFlood`, `consumeFailedPut` and `hsInitNoPeer`
  (section 2.4). `hsWasUnderLoad` and `macNoCookieCheck` take one outcome
  per flood and are not declared. **What
  this weakens:** a `repeatable` declaration applies in every operation,
  so for those decisions "reported more than once" and "opposite outcome
  covered" no longer fire anywhere; their per-packet reports collapse
  into outcome sets, as the batch's do. Per-packet precision then rests
  on the record stream (each packet's clock record consumed in order at
  its exact site: exact) and on the operand rows (one-directional), not
  on control flow. "Outcome not witnessed" and the order rule within a
  function still apply. A per-operation variant (the exemption extended
  to the opposite-outcome rule for `wg_flood` only, with no `repeatable`
  declarations) would be narrower; its cost is a second exemption on the
  opposite-outcome rule, which today has none. [AGENT] The design names
  the `repeatable` route, the precedent being the W7 tier's declarations
  (`Decision.lean:2970-2974`), and puts the choice to the user in U1.
- The merged-injection control **stays**. `corpus/underload-controls/e_underload_merged`
  (`scripts/steering-controls.py:37,79`) has the guest process a valid
  initiation the Runner ignores (`Runner.lean:646-650`); under the exact
  execution the run diverges at that packet's first cookie record and at
  the counter's operand, and the control's expected detail is updated to
  that. No miscount control (it would need a seam that feeds the mirror
  an input other than the guest's; none exists and none should) and no
  positive "control valid" trace (the guest places the control right after
  the leading valids, `guest.c:1588-1593`, which is `e_underload_two_replies`).

This answers the E design's C1: the summary and the discard existed
because a site-level skip of site 6 would eat the injection's own record.
The exact execution has no skip at all; every record is consumed at its
own site in order, an operation's records end at the operation, and
`requireDrained` stops a worker that outlives the wait. A merged or extra
packet diverges the per-packet sequence. The guard is kept and stronger.

What stays environment: the template's bytes, the submission's order and
the guest's wait after the submission (`QUEUE_WAIT_US`, 100 ms, inside
the operation). Nothing moves into the mirror that is not the C's.

### 2.4 The measurement: what was measured, and the build's first step

`e_underload_live` (520 invalid packets, no leading valid, then an
injection inside the decay) and `e_underload_ratelimit` (520 invalid,
two leading valids), one run each on s4, the summarised path and the
exact flag's path (`check.py --suite wireguard --trace <id>`, the second
with `LEANUX_FLOOD_EXACT=1 --no-build`). **What the exact flag's path
is:** the producer side discarded as in the summary, the counter preset
to the batch's size, control flow skipped by the checker's `wg_flood`
arm, the tail run through the real worker. It is not the design of
section 2.3; the figures below say what that path consumed and reported,
no more.

| `e_underload_live`, operation 3 | summarised | exact flag |
| --- | --- | --- |
| verdict | agreement, 7 operations | agreement, 7 operations |
| remote records of the flood (pc child), the kernel's count | 1,565: 520 clock reads (9 at `:115`, 511 at `:117`), 521 section starts and 521 stops (520 producers, one worker), 2 resched, 1 queue | 1,565, the same kernel count |
| of which consumed by a mirror unit | 524 (the worker's section bracket, the leading valids' records: none here) folded by `floodTailEffect`; 1,041 discarded | 524 by the worker; 1,041 still discarded |
| mirror branches reported for the flood | 1 | 5,703 |
| operand pairs matched / distinct rows (trace) | 18 / 14 | 1,049 / 536 |
| the mirror on the recorded inputs (`scripts/in-bundle .lake/build/bin/leanux-model`) | 0.09 s | 0.10 s |

`e_underload_ratelimit`, exact flag: agreement, 5,885 branches for the
flood, 1,061 pairs over 544 rows, 0.10 s against 0.09 s.

What these figures do show: (a) with 520 queued the counter is at or over
512 for the first 9 packets only, so the tail is 9 reads at `:115` and
511 at `:117`, and the exact path consumed each in order at its site
(the worker half of the design is exact and agrees); (b) `operand_agreement`
is not skipped for the flood, so the 1,049 pairs include 520
`hsUnderLoad` and 511 `hsDecayExpired` obligations, each matched by a
kernel row: the per-packet counter values the mirror computed agree with
Linux's in that direction; (c) the worker half costs the mirror about
10 ms for 520 packets. What they do not show: the producer side through
`Env.batch` (never ran), the batch-before-worker fact from records (the
counter was preset), the 5,703 branches against coverage (control flow
was skipped; section 2.3 says the checker would reject them unchanged),
and the cost with producers (an estimate: about 11 labels per packet on
the worker, 6 on the producer, so about 9,000 labels for 520 against
`MAX_BRANCHES = 262144`, `protocol.py:230`).

**The build's first step** [AGENT]: prototype `Env.flood` over
`Env.batch` with the checker rules of section 2.3, run the thirteen
`corpus/wireguard` flood traces and the control
(`check.py --suite wireguard` on those ids, one claim-point-sized run),
and restate this table from that run before U1 goes to the user. Stop
condition: **report rather than fix if the exact path mismatches** on any
of the thirteen (a producer section where the mirror expects none, a
counter operand that differs, a worker that outlives the wait): the
mismatch is a finding about the batch's assumptions or the mirror, not
something to absorb in the wrapper.

The report bound: a 520-packet flood reports about 9,000 labels, the W7
tier's 1,024-item batch reports 126,531, so a flood of a few thousand
packets is inside the bound and a 16,384-packet one is not (the harness
allows `2^20`, `harness/trace.py:444`). The bound becomes the flood's
size limit, declared in the trace validator: enough for the 511/512/513
boundary and for the 2,050-packet busy trace.

**The prototype run (2026-10-15, B4 part 2, on s4).** `Env.flood` over
`Env.batch` with the three checker rules, the sixteen flood traces (the
thirteen plus `e_underload_busy`, `l_delete_ratelimited6` and
`l_recreate_ratelimited6` from part 1) and the control:

| Trace | Outcome | Flood labels | Note |
| --- | --- | --- | --- |
| `e_underload_flood`, `_cookie`, `_two_replies`, `_cookie_rotated`, `_live`, `_decayed` | agreement | 19,223 to 19,333 | first run |
| `e_underload_511`, `_512`, `_513` | agreement | 17,997 to 18,998 | first run |
| `e_underload_busy` (2,100) | agreement | 74,523 | first run; the busy arm from the 2,050th packet |
| `e_underload_ratelimit`, `l_delete_ratelimited` | agreement after two declaration changes | 19,457 | first run: "opposite outcome covered" for `consume_initiation.flood`, `.failed_put`, `initiation_no_peer`: the second leading initiation is dropped by noise.c's 50/s test where the first was consumed, both outcomes in one operation; declared `repeatable` |
| `e_underload_ratelimit6`, `_ratelimit6_deny`, `l_delete_ratelimited6`, `l_recreate_ratelimited6` | agreement after the same, plus `make_cookie.ipv4`'s witness corrected | 19,378 to 19,763 | the only PC attributed to cookie.c:108 is the IPv6 arm's block entry, covered by every IPv6 `make_cookie` and by no IPv4 one (the coverage maps of both families, and `objdump -l`); the declaration witnesses :110-111 now and leaves the IPv4 arm unobservable |
| `e_underload_merged` (control) | rejected: `unsupported_path`, "work the flood queued outlived the guest's wait" | | the kernel's extra producer section stands where the mirror expects the worker |

Records: the exact flood consumes every remote record of the operation
(no discard); the hidden streams agreed on every trace (no hidden
mismatch anywhere in the run). Labels: about 37 per packet, producer and
worker, so the validator's bound of 4,000 packets (the ring's 4,096)
stays inside `MAX_BRANCHES`. The `repeatable` list is nine decisions, not
the six of section 2.3: the consume path's three were found by the run.
The one-off mutant B4-M1 (the receive worker's yields ignored) is
rejected by `e_underload_busy` and `e_underload_live` (a hidden mismatch at
the resched record, site 60). The whole `wireguard` suite on the final
build is reported in the part-2 commit.

### 2.5 The busy test and the trylock (`:554-558`)

The producer's other read of the counter is `> MAX/2`, that is 2,048
(`messages.h:51`; the mirror has it right, `Receive.lean:473`): the
`.rxQueueBusy` arm (`Decision.lean:1147`), reached as true by the k-th
produce when k - 1 > 2,048 are queued, so the smallest batch that takes
it once is 2,050. Today the arm stops as unsupported because
`spin_trylock_bh`'s outcome is "the worker's lock state at that instant,
which no record carries" (the receive audit). That reason is wrong about
the lock: the trylock is on `producer_lock` (`receive.c:555`), which only
producers take (`ptr_ring.h:160-164`); the worker consumes under
`consumer_lock` (`ptr_ring.h:362-368`), so its position is irrelevant.
And on this configuration the outcome is constant: with `CONFIG_SMP` and
`CONFIG_DEBUG_SPINLOCK` off, `arch_spin_trylock` is `({ barrier();
(void)(lock); 1; })` (`include/linux/spinlock_up.h:56`): the trylock
always succeeds. [AGENT] B4 declares the arm's outcome so, keyed to the
configuration (a `CONFIG_SMP` oracle would need a record), and the
`.rxQueueBusy` true arm produces under the trylock exactly as the plain
path does. The trace `e_underload_busy` is a flood of 2,050 or more
(2,100 proposed: the arm taken 51 times, about 36,000 labels, inside the
bound). `rxProduceFailed` under the trylock (the ring full at 4,096) stays
out of reach by the size limit of section 2.4.

### 2.6 Decisions and operands

No new decision on the under-load path. The decisions that become checked
per packet, under the rule of section 2.3: `hsUnderLoad` (520 distinct
operand obligations per flood), `hsWasUnderLoad`, `hsDecayExpired`,
`hsCookie`, the `packet_needs_cookie` arms, the MAC1 outcome
(`cookieValidatePacket`'s decisions), and on the producer side
`wg_packet_receive`'s handshake arm, `.rxQueueBusy`, the produce and the
queue. The comparison child's area holds the rows (a `wg_create` window
already exceeds that count by far).

## 3. Question 2, the GC: deferred to its own stream

### 3.1 What stands

The GC runs in every WireGuard trace today, unobserved. The timer is
armed at `wg_create` for `jiffies + 250` and re-armed by each run; the
work function is not in `DISPATCH_SYMBOLS`, so no section opens, the
clock read at `:57` is written in no recording context, and the requeue's
`add_timer_global` bypasses the arm hook even for an armed function.
Measured on `e_underload_live` (section 2.4's run): the end-of-wait reads
give `4294892911` after `wg_set` and `4294893291` after the last
injection, 380 ticks (1.52 s) from an instant already after the device's
creation (the cmp child: 523 ticks; `timing.jsonl`: 1.49 s and 2.03 s
since `wg_up`). So at least one run per trace, two in the cmp child, with
the tables empty. A run with entries would free an entry idle for more
than a second, and the next handshake from that source would insert
(site 133) where the mirror, holding the entry, predicts a hit (site
132): a hidden mismatch, fail-closed. That is why the ratelimiter traces
keep their second initiation within the same tick and no trace advances
past a second with an entry in the table. The exclusion is safe; it
bounds the corpus; `gcEntries true` (`Leanux/WG/Device.lean:144-161`)
stops as unsupported and is never reached.

### 3.2 The exclusion, kept, with its reason sharpened

The first version of this note designed the GC as a dispatched unit. The
review found three defects in that design and four rules it lacked, each
checkable against the C or the harness; the GC therefore leaves this
stream, and the reason the E design's section 11 gives ("its firing is
outside the trace's windows on this fixture and no record names it") is
sharpened to the following, which a later stream must overcome:

1. **The arm record would carry no WireGuard site.** The arm happens in
   `__queue_delayed_work`, which is out of line in the oracle
   (`System.map`: `ffffffff81090570 t __queue_delayed_work`, called from
   `queue_delayed_work_on`), so `_RET_IP_` there is an address in
   `kernel/workqueue.c`, the same for the init's arm (`:191`) and the
   requeue (`:81`). A hook must either pass the outer return address
   from `queue_delayed_work_on` and `mod_delayed_work_on` (both exported;
   the WireGuard callers inline `queue_delayed_work`) or declare one
   `workqueue.c` site and tell the two arms apart by mirror state.
2. **A requeue during the cancel arms nothing.** `cancel_delayed_work_sync`
   disables the work before flushing a running instance and re-enables it
   only afterwards (`workqueue.c:4386`, `:4400-4401`); a
   `queue_delayed_work` issued meanwhile sets PENDING and has it cleared
   by `clear_pending_if_disabled` (`:2585-2586`, `:2386-2399`) without
   queueing and without reaching any arm hook. Every `wg_delete` that
   meets a run in progress sees no arm record. The state needs the
   disable count across the cancel and the arming rule needs the test.
3. **The inter-operation gap is loud, not silent.** The first version
   said a section landing between one operation's remote read and the
   next operation's reset "is lost, silently" and called this an
   instrument gap that B4 would close. **That claim is retracted.** The
   guest reads the kernel's count of opened sections after the trace
   (`guest.c:1480-1484`) and `section_problems` (`check.py:653-667`,
   since 0437dbc, 2026-10-04) fails the trace with "dispatch sections
   opened but not recorded" when the recorded starts fall short. The
   per-operation reset dates from 2026-10-01 and the `wg_observe`
   exception from 2026-10-06; since sections exist, nothing in a gap has
   been able to pass silently. The integration record must not carry this
   as a found gap. What the gap does mean for a GC stream: once the GC is
   armed in a trace, a firing in any window outside a reset-to-read span
   is a frequent loud failure, and a gap rule must close every such
   window: the head (records before operation 0, after the dispatch
   load, stated to belong to it), the gaps between operations, and the
   tail (after the last read the child runs `delete_wg0`, `guest.c:2727`,
   `:2755`, whose `cancel_delayed_work_sync` comes last; a firing there is
   opened and never recorded, so a trailing idle segment the mirror
   consumes is needed). Never resetting has a capacity cost: `CAPACITY`
   is 4 Mi words (`guest.c:51`), the comparison child's records are four
   words each, and `full_remote_kcov` (`:2676`) would trip on the
   cumulative count; a trace with a large batch, a large flood or several
   `wg_create` windows needs numbers. (The first version also said no
   peer timer lands in a gap because "their delays are 5 s and up"; that
   is not the reason. The peer timers' natural firings land in operations'
   waits by the trace bound and the advances, and `section_problems`
   catches one that did not.)
4. **No rule detects a missing firing.** "Consumed where the records
   place them" accepts the sections present and rejects none absent: the
   GC's timer and work addresses are constant (`gc_work` is static), and
   a stale pending timer passes the next firing's due test. The peer
   timers share this property today (`runTimers`, `Env.lean:406-441`). A
   GC stream needs a completeness rule wherever the mirror knows
   `jiffies` (the kind-310 reads, the 303 arms, the 311 reads): a pending
   GC timer due by then must already have fired, respecting the wheel's
   rounding (section 1.3: the timer fires in `(E, E + 8]`), and either
   arguing away a softirq deferred to `ksoftirqd` or stating it as a
   residual. The strict due test `time_before(expires, J)` is sound for
   the same rounding-up reason.
5. **The nested firing is common, and its run's placement is unrecorded.**
   A tick's `TIMER_SOFTIRQ` runs before `NET_RX` in the same
   `handle_softirqs` pass, including at the `local_bh_enable` of every
   loopback send inside the trace task's system call, so a GC firing
   nested in a task section is as frequent as the fraction of time spent
   in task sections and system calls, times about four firings per trace.
   The trace task's yields are unrecorded (`kcov_dispatch_resched` writes
   only inside a dispatch section, `gen:586-600`), so a sleep or
   `cond_resched` inside a system call runs the GC's run mid-call, placed
   by sequence order alone. The mirror has no rule for an ambient
   dispatched unit with content at an arbitrary read, and a first-day
   spike over the full WireGuard suite is needed to measure how often the
   case occurs before any rule is written.
6. **The activation machinery covers queue-draining workers only.**
   `Activation.hasWork`, `iter` and `occupancy` (`Leanux/Env/Batch.lean:141-152`,
   `:201-227`) are over the encrypt, decrypt, receive and tx workers, with
   "not a draining worker" invariants for everything else. A 2,048-bucket
   walk with a resched point per bucket, resumable after a yield, is a
   new activation kind with its own fuel and consistency test.
7. **Slot 14 is reserved.** `Defs.lean:950-956` reserves indices 14-15
   for "W5-W6's two units"; W5 and W6 landed (`docs/2026-10-06-w5-w6-receive.md`)
   and `DISPATCH_SYMBOLS` has fourteen entries, so whether the reservation
   is dead is for the GC stream to settle with the interface's owner
   before taking the slot, and the comment updated either way.

### 3.3 What a later GC stream must meet

Named here so the stream's charter can start from them:

- **Per-trace arming.** `wg_ratelimiter_gc_entries` armed only in the GC
  traces (`arm_masks`, as `cleanup_net` is armed for foreign-creator
  traces), never in every WireGuard trace: no existing verdict depends on
  the new placement rules until they have paid their way.
- **The spike first.** One guest run measuring, per WireGuard trace, the
  wall time outside the reset-to-read spans (the gaps plus the tail) and
  how often a tick's softirq lands inside a task section: the failure
  rate a GC armed everywhere would cause under today's guest, and the
  size of the nested case.
- **The arm record's attribution** (item 1), **the disable state** across
  the cancel (item 2), **the head, tail and capacity rule** of the guest's
  window (item 3), **the due-means-fired completeness rule** respecting
  the wheel's rounding (item 4), **the nested-section rule** sized by the
  spike (item 5), **a new activation kind** for the walk (item 6), **the
  slot** (item 7).
- The representation the first version proposed and that survives the
  review, for reuse: `Kernel.ratelimiter.gcTimer`/`gcPending` with the
  firing named by the delayed work's function in `call_timer_fn`'s hook
  (`fn == delayed_work_timer_fn ? container_of(timer, struct delayed_work,
  timer)->work.func : fn`, record-only, no armed work function being a
  delayed work today; `linkwatch_event` is one but no trace arms it, and
  W8b inherits the firing sections when it does), the run's section as
  `gcEntries true` with two new comparison decisions (`gcV4EntryExpired`
  at `:66`, `gcV6EntryExpired` at `:72`, operands `(now - last_time_ns,
  NSEC_PER_SEC)`), the RCU-deferred decrement of `total_entries` declared
  unobservable under the out-of-reach limit, and the traces
  `e_underload_ratelimit_gc`, `e_underload_ratelimit_gc_kept`,
  `e_underload_ratelimit6_gc`.

### 3.4 The interface requirement on the timer representation (B3), extended

Written against the interface, not B3's note (not read), for the GC
stream's use; B4 itself now needs nothing from B3.

- **R1, an owner beside the peers.** A kernel-global timer with
  `expires`, pending or not, armed and deleted by the ratelimiter's code.
- **R2, the arm.** The same consumption shape as `armTimer`'s: a kind-303
  record `{jiffies, expires, timer}`, `expires = jiffies + HZ` checked
  (the caller's read is the same instant, `workqueue.c:2548`), the
  timer's address registered as the unit; **with the attribution of
  section 3.2 item 1** (the outer return address, or one `workqueue.c`
  site told apart by state).
- **R3, the firing.** A record-placed section whose due test is
  `time_before(expires, J)` for a `J` the mirror knows, or, under a wheel
  representation, the wheel's own order; **the wheel model must place the
  GC timer by `calc_wheel_index` like the peers'** (level 1, granularity
  8, firing in `(E, E + 8]`), the deferrable flag being irrelevant to
  placement on this configuration (one base).
- **R4, deletion** at `cancel_delayed_work_sync`, from state, no record.
- **R5, nesting.** The firing may land inside a task section.
- **R6, the pairing.** The timer unit armed by the 303 record and consumed
  by the firing section; the work unit by the 307 record inside it and
  the run's section (`dispatch_problems`, `check.py:748-798`).
- **R7, completeness.** A due timer must have fired by any known
  `jiffies`, with the rounding and the `ksoftirqd` residual stated.
- **R8, the disable state** during `cancel_delayed_work_sync`: a requeue
  while disabled arms nothing and records nothing.

### 3.5 The two-table uninit defect: fixed in this build

Found reading (Rule Zero, clause 1), confirmed by the review. `gcEntries`
with `work = false` empties `table` only and reports `gcV6EntryIter`
false always (`Device.lean:152-158`), and `ratelimiterInit` resets
`table` only (`:128`); the C's uninit walk empties both tables
(`ratelimiter.c:64-74`). After a delete with IPv6 entries and a re-create,
the mirror holds entries the kernel freed. It could not have hidden a
wrong verdict: a delete with IPv6 entries makes the kernel cover `:73`
against the mirror's `gcV6EntryIter=0` ("opposite outcome covered"), and
a re-create followed by a lookup from the same `/64` gives site 132
against 133. No corpus trace has IPv6 entries followed by `wg_delete`
(`l_delete_ratelimited` is IPv4), so the defect has been invisible. The
docstring of `gcEntries` ("an IPv6 handshake is `unsupported`", `:138`)
predates F12. B4 fixes both tables in `gcEntries` and `ratelimiterInit`
and the docstring, with two traces: `l_delete_ratelimited6` (an IPv6
entry, then `wg_delete`: the uninit's v6 arm, which fails before the fix
and passes after) and `l_recreate_ratelimited6` (then `wg_create`,
`wg_set`, `wg_up` and an initiation from the same `/64`: an insert). This
is independent of the GC and lands with questions 1 and 3. Campaign 1's
`WGCookie.lean` frame already views both tables
(`Framing/WGCookie.lean:19`): the frame was right and the mirror behind
it.

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

`ratelimiterAllow` (`Receive.lean:153-200`; the branch at `:189`):
`branch .rlAllocFail !(← envOk .ratelimiterEntry)` and the arm
`unsupported`. `envOk` is the pipes-era environment oracle (`EnvSite`,
`Defs.lean:697-709`), which always answers success. The E design's section
11 and the comment at `Receive.lean:184-188` say the site "is not in the
kind-305 hook's list (`kernel/patches/gen-choice-stream.py`)". There is no
such list: `__kcov_alloc_pre` tests `canonicalize_ip(addr)` against the
loaded ranges (`gen:1475-1478`), the ranges come from `ALLOC_SITES` rows
through `objdump` (`steer.py:250-298`), and `wg_ratelimiter_allow` calls
`kmem_cache_alloc_noprof` directly (`ffffffff813a1c80` in the oracle).
What is missing is the site's row and its `AllocSite` constructor. B4
corrects the sentence in the E design, the comment, and the receive
audit's F13 row.

### 4.3 The change: no kernel change

- `AllocSite.kmemCacheAllocRlEntry`: consumer `drivers/net/wireguard/ratelimiter.c:138`,
  a direct site (`kmem_cache_alloc_noprof` is in `ALLOC_ENTRIES`,
  `steer.py:161`), `.exact 1`, hidden id `70 + index`; the `ALLOC_SITES`
  row with `cls='kworker'`, like `kzallocKeypair` (`noise.c:100`,
  `steer.py:219`): the receive worker's context.
- `ratelimiterAllow` consumes it with `hiddenAlloc`; the false arm is the
  C's `err_oom`: the counter back by one and `return false`, so
  `cookieValidatePacket` returns `.ratelimited` and the packet is
  dropped. The arm is modelled, not `unsupported`. `EnvSite.ratelimiterEntry`
  is deleted.
- Arming. A chunk is armed for a site when a trace steers it or the run's
  `arm` lists it (`check.py:1568-1578`); `hiddenAlloc` answers success
  unarmed (the A design's transitional rule, 6.6, still in force:
  `Defs.lean:2211`). The ratelimiter traces (`e_underload_ratelimit*`,
  `l_delete_ratelimited`, the two uninit traces of section 3.5) declare
  the site with a `draw` entry, which `alloc_refusal` accepts for the
  `kworker` class (it returns before the class gate, `steer.py:310-311`),
  so their chunk records it and the mirror consumes the record; the
  success outcome is then checked, not assumed.
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
| the clock per tail packet (`:115`, site 130; `:117`, site 6) | folded by `floodTailEffect` | consumed by the worker per packet, in order |
| the producer sections and the IP-layer draws of a flood | discarded by `discardFloodRecords` | consumed by the producer per packet (`Env.batch`) |
| the flood's queue and resched records | dropped | consumed (the first packet's queue, the worker's yields) |
| the counter at `:112` | derived; its compare's operands recorded, the tail's unreported | derived; reported and matched per packet (one-directional) |
| the entry allocation (`:138`, kind 305) | `envOk` | a declared site, consumed when the chunk is armed |

No new record kind. No oracle change: B4 lands on s4. The GC's records
(sections, queue, arm, the `:57` clock) are the GC stream's.

## 6. Environment rules touched

- `Env.flood`: rewritten over `Env.batch`; the summary, the discard and
  the exact flag deleted (section 2.3); the drain check gains the
  handshake queue and the counter.
- The decay: unchanged in the mirror (`receiveHandshakePacket`); the
  environment no longer folds it.
- The busy arm's outcome: constant on this configuration (section 2.5),
  a declared fact of the environment, not a record.
- Nothing else. The GC's placement rules of the first version are
  withdrawn with the GC.

## 7. Decisions and operands added

| Decision | Site | Operands | Note |
| --- | --- | --- | --- |
| `.rxQueueBusy` true arm | `receive.c:554-558` | none new | the trylock constant on this configuration (section 2.5) |
| `.ratelimiterInit{Cache,TableV4,TableV6}Err` | `:165`, `:180`, `:185` | none | constant false with the reason |
| `.rlAllocFail` | `:139` | none | over the record; the true arm modelled |
| `repeatable` on `hsUnderLoad`, `hsWasUnderLoad`, `macInvalid`, `macNoCookieCheck`, the `packet_needs_cookie` arms, `rxQueueBusy` | | | the checker rule change of U1 |

No decision is removed. The GC's two comparison decisions belong to the
GC stream.

## 8. One-off mutants

| Mutant | Rejected by |
| --- | --- |
| the mirror ignores the resched records of the flood's worker (runs it in one activation) | the W7 interleaving: a producer section between activations is consumed in the wrong order, hidden mismatch |
| the under-load threshold at 511 in the exact flood | `e_underload_511/512/513` (the boundary traces) |
| `envOk` kept for the entry while the chunk is armed | an unconsumed record |

Each run once in its commit and deleted; none replaces a sentinel.
`scripts/wg-mutants.py` holds thirteen sentinels and none for E
(`:36-121`); nothing about the sentinel set is claimed.

## 9. Corpus

Additions: `e_underload_busy` (2,100), `l_delete_ratelimited6`,
`l_recreate_ratelimited6`. Kept: `e_underload_merged` with its expected
detail updated. Changes: none to existing traces. The suite's run time is
unchanged in any measurable way (section 2.4). The GC traces of section
3.3 belong to the GC stream.

## 10. Proof-tree frames touched, and the repair's cost

Read-only, by `git grep` and `git show` on `main` (ca6b22e),
`proofs/campaign` and `proofs/campaign-2`.

**Statement edits** (deleting `executeTrace`'s `floodExact` parameter).
On `proofs/campaign` the statements quantify over it explicitly
(`{floodExact : Bool}` and the argument): `WG/AntiReplay/Statements.lean:29-41`
(`runner_uniqueness`, `runner_floor`: register results, so the edit is
named as a statement edit under Rule Zero), the carried
`WG/ReplayWindow/Statements.lean:16-18` (`S1`), `Logged/Runner.lean:12-122`,
`Logged/Checkpoints.lean:41-156` (`executeTraceCheckpoints`),
`WG/Keypairs/Evolution/{Bounds,Runner,Syscalls}.lean`,
`WG/Lifetimes/EnvTrafficAudit.lean:125`, `Logged/Operations.lean:314`.
On `main` and `proofs/campaign-2` the statements use the default argument
(`Logged/Runner.lean`, `WG/ReplayWindow/Statements.lean:17-20`,
`Evolution/{Runner,Syscalls}.lean`, campaign 2's `Progress/BatchBacklog.lean:42`):
no statement text changes there, the parameter's removal being
transparent.

**Deleted with their subjects.** Campaign 1: `Framing/EnvOperations.lean:78-85`
(`floodTailEffect_sameKernel`), `Framing/Kernel.lean:247-252`
(`discardFloodRecords_sameWGKernel`, `_spec`), `WG/Keypairs/Frames/Kernel.lean:219-224`.
Main and campaign 2: `WG/Keypairs/Frames/Kernel.lean:179-184` (the same
frames). `Env.flood`'s own frame (`WG/Keypairs/Frames/Env.lean:29-36`,
all three trees) is re-proved over `Env.batch`'s frames, which the trees
already hold for `wg_batch`.

**Re-mirrored copies** (`floodLogged` and the prefix copies of the flood
and of `packetReceive`). Campaign 1: `Logged/Operations.lean:284-350` (its
`floodLogged`, with `family`), `WG/Lifetimes/EnvTrafficAudit.lean:83-136`
(`floodQueue`, `auditFloodReset_preserves`, the prefix copy at `:120-135`),
`WG/Lifetimes/ReceiveIngress.lean:54-58,83-88` (the `packetReceive`
prefix with the busy arm). Main and campaign 2: `Logged/Operations.lean:255-303`
(`floodLogged` without `family`: campaign 2's copy already lags main's
`Env.flood` by F12's parameter), `WG/Keypairs/Evolution/Operations.lean:41-43,119-121`
(`floodLogged_evolves` and the `discardFloodRecords`/`floodTailEffect`
`ordinary_head` steps).

**Re-runs.** `ratelimiterAllow`'s frames (campaign 1
`Framing/WGCookie.lean:55-78`; `WG/Keypairs/Frames/WGMore.lean:317-322`
on main and campaign 2, `:326-331` on campaign 1): `hiddenAlloc` replaces
`envOk`; `packetReceive_ordinary` (`WGMore.lean:460`, all three trees)
for the busy arm; the ratelimiter lifecycle frames (`Framing/WGDeviceLifecycle.lean:13-51,126`
on campaign 1; `WG/Keypairs/Frames/WGDevice.lean:45-64,81,135` on main
and campaign 2, `:53-72,150` on campaign 1; `WG/Lifetimes/DeviceLifecycle.lean:24,62,80`
on campaign 1) for the two-table `gcEntries` and the constant init arms.
Unaffected: campaign 1's `Cookies/Load.lean`, `Cookies/Gate.lean` and
`FloodResistance/Statements.lean`, which are over `loadPhase` with the
counter as a hypothesis, and the `envOk` frames of the pipe paths
(`envOk` itself stays).

**On `main`,** `LeanuxProofs` is the import closure of `Leanux/Proofs.lean`
(`lakefile.toml:10-11`), which is `ReplayWindow.Statements` and
`Counterexamples`; `Statements` imports `Keypairs.Evolution.Runner` and
`Syscalls`, whose closure holds `Frames/Env.lean`, `Frames/Kernel.lean`,
`Frames/WGDevice.lean`, `WGMore.lean`, `Evolution/Operations.lean` and
`Logged/Operations.lean`. So the register's one current result
(ReplayWindow) lags at B4's landing until those are repaired; the
integration record says so and the repair is a follow-on on the proof
tree, per the register rule.

**Cost of the repair** [AGENT]: main, about 0.5 day (the frame deletions,
`Env.flood`'s frame over `Env.batch`, the `floodLogged` re-mirroring, the
re-runs); campaign 2, the same edits on the same files plus its
`BatchBacklog` re-run, about 0.5 day, done as a carry when it next merges
main (the `family` lag is repaired in the same pass); campaign 1, the
statement edits (mechanical, nine files, about 0.25 day) plus its own
`floodLogged` and prefix copies and the lifecycle frames, about 0.75 day,
as a carry. About 1.75 agent-days across the three trees, none of it a
condition on B4's landing.

## 11. Risks

1. **The exact flood path mismatches on a corpus trace** (the build's
   first step, section 2.4). A producer section where `Env.batch` expects
   none, a counter operand that differs, a worker that outlives the wait:
   reported, not fixed in the wrapper; the design is re-put to the user
   with the mismatch.
2. **The checker rule change weakens control flow for the declared
   decisions in every operation** (section 2.3). Named in U1 with the
   narrower per-operation alternative; the user chooses.
3. **The report bound.** A flood above a few thousand packets exceeds
   `MAX_BRANCHES`; the validator refuses it with the reason. Enough for
   511/512/513 and for 2,100.
4. **The proof-tree lag** (section 10): the register's one result lags at
   the landing; the repair is costed and is a follow-on.
5. **The GC stays excluded**, with the corpus bound it implies (no trace
   advances past a second with a ratelimiter entry in the table), until
   its own stream lands.

## 12. Estimate (questions 1 and 3 plus the uninit fix)

About 2.25 agent-days, roughly 0.1 WU (one WU being WireGuard's three
weeks, `docs/2026-10-12-kernel-scout.md`):

| Part | Days |
| --- | --- |
| the flood over `Env.batch`, the deletions, the checker rules, the control's updated detail, the busy arm, `e_underload_busy`; the prototype run over the thirteen flood traces and the control as the first step | 1.5 |
| the entry allocation site, the init's constant arms, the docs (E design 11, the receive audit's F13, the census rows 132 and 135, `docs/decisions.md`), the three one-off mutants | 0.5 |
| the two-table uninit fix, its docstring, `l_delete_ratelimited6` and `l_recreate_ratelimited6` | 0.25 |

No oracle rebuild and no new identity: the claim point is the full
check, controls and sentinels on s4. The proof-tree repair (about 1.75
days across the trees, section 10) and the GC stream (3 to 5 days plus
its claim point, by the review's count, section 3) are separate.

## 13. Decisions: the user's, and tactical

For the user:

- **U1.** The flood becomes a `wg_batch` in the mirror; the summary, the
  discard, the exact flag and the checker's `wg_flood` arm are deleted;
  and **three rules on the trust surface change** (section 2.3):
  `wg_flood` joins `wg_batch` in the file restriction and in the repeat
  rule's exemption, and the flood path's decisions that take both
  outcomes in one operation are declared `repeatable`, which weakens
  "reported more than once" and "opposite outcome covered" for those
  decisions in every operation (the per-operation variant is the
  alternative). The merged-injection control is kept with its detail
  updated. The prototype run over the thirteen flood traces and the
  control precedes this decision (section 2.4).
- **U2.** *Withdrawn.* The GC leaves this stream (section 3); there is no
  oracle change and no guest window change in B4. A GC stream's charter
  puts its own decisions.
- **U3.** *Withdrawn with U2.* Its content, the stop condition for the
  nested-section rule, becomes the GC stream's.

Tactical [AGENT]:

- no record kind for the counter (section 2.2);
- the trylock constant on this configuration, keyed to it (section 2.5);
- the entry site record-only, no `kworker` steering class (section 4.3);
- the init's three allocations constant-false with the reason, census
  row 132 unchanged (section 4.4);
- the two-table uninit fix and the docstring, with `l_delete_ratelimited6`
  and `l_recreate_ratelimited6` as its witnesses (section 3.5);
- the flood size limit at the report bound (section 2.4);
- the three one-off mutants (section 8).

## 14. Review dispositions

Against [the review](2026-10-15-design-b4-review.md), one by one. "Fixed"
means the note now says what the finding asked, at the section named;
"answered" gives a reason the reader can check; "raised" puts it to the
user.

1. **Fixed** (section 2.4). The measurement is restated as the exact
   flag's path: the discard kept (`Env.lean:812` precedes the branch at
   `:821`), the counter preset (`:828`), control flow skipped
   (`check.py:1043-1059`), 9 reads at `:115` and 511 at `:117` (520
   queued, the counter at or over 512 for the first 9), the kernel's
   record count fixed whatever the mirror does, the 10 ms the worker half
   only. The prototype over the thirteen flood traces and the control is
   the build's first step with "report rather than fix if the exact path
   mismatches".
2. **Fixed** (sections 2.3, 13). The checker change is named in U1 as
   three trust-surface rules: the file restriction (`check.py:1066`), the
   repeat rule's exemption (`:1095-1106`) and the `repeatable`
   declarations (`Decision.lean:2959-3065`: none of the flood path's
   decisions is repeatable today), with what they weaken and the
   per-operation alternative.
3. **Fixed** (section 2.2). The operand instrument is stated as
   one-directional (`check.py:1241-1246`; `operand_rows_distinct` a
   report counter, `:1857`, `:1908`); the per-packet completeness
   argument now rests on the in-order clock records.
4. **Fixed** (section 2.5). The threshold is 2,048 (`messages.h:51`,
   `Receive.lean:473`); the trylock is on `producer_lock`
   (`receive.c:555`, `ptr_ring.h:160-164`), the worker's `consumer_lock`
   irrelevant (`ptr_ring.h:362-368`); the outcome is constant on this
   configuration (`spinlock_up.h:56`, no `SMP`, no `DEBUG_SPINLOCK`); the
   trace is 2,050 or more (2,100 proposed).
5. **Fixed** (section 8). No sentinel claim; `scripts/wg-mutants.py` has
   thirteen sentinels and none for E; a one-off mutant for the exact
   flood's threshold at 511 is added, rejected by the boundary traces.
6. **Fixed** (sections 2.3, 9). `e_underload_merged` is kept (the Runner
   ignores `control`, `Runner.lean:646-650`; the run diverges at the
   control's first cookie record and the counter's operand); the miscount
   control and the "control valid" trace are dropped (the latter is
   `e_underload_two_replies`, `guest.c:1588-1593`).
7. **Fixed as a reason for the exclusion** (section 3.2 item 1). The GC
   leaves the stream; the attribution fact is recorded for its charter
   (`System.map`: `__queue_delayed_work` out of line), the `workqueue.c`
   lines corrected (section 1.3: `:2548`, `:2555`, `:2558`, `:2560`;
   `clear_pending_if_disabled` `:2386-2399`, `:2585-2586`).
8. **Fixed as a reason for the exclusion** (section 3.2 item 2, section
   1.3). `cancel_delayed_work_sync` disables the work
   (`workqueue.c:4386`, re-enabled `:4400-4401`), so a requeue during the
   cancel arms nothing; the first version's "arms a timer that the cancel
   then deletes" is withdrawn; R8 added (section 3.4).
9. **Fixed, with the claim retracted** (section 3.2 item 3). The gap is
   loud: `section_problems` (`check.py:653-667`) against the kernel's
   opened count (`guest.c:1480-1484`). The note says so explicitly, says
   the integration record must not carry it as a found gap, and records
   the head, tail (`delete_wg0`, `guest.c:2727`, `:2755`) and capacity
   (`CAPACITY`, `:51`; `full_remote_kcov`, `:2676`) requirements for the
   GC stream. The mutant is withdrawn (`gc_work` is static; the phase is
   uncontrolled). The "5 s and up" sentence is withdrawn; the file's
   persistent-keepalive trace carries `"keepalive": 5`, not the 2 s the
   review names, which does not change the point.
10. **Fixed as a requirement** (section 3.2 item 4, R7). The
    due-means-fired rule with the wheel's rounding (`timer.c:579-581`,
    level 1, granularity 8) and the `ksoftirqd` residual.
11. **Fixed as a requirement** (section 3.2 item 5, section 3.3).
    Per-trace arming and the suite-wide spike first; the trace task's
    yields are unrecorded (`gen:586-600`), so the run's placement rests
    on sequence order.
12. **Fixed as a requirement** (section 3.2 item 6). The activation
    machinery covers the four draining workers (`Env/Batch.lean:141-152`,
    `:201-227`); the walk is a new activation kind.
13. **Fixed as a requirement** (section 3.2 item 7). Slot 14 is reserved
    (`Defs.lean:950-956`); whether the reservation is dead (W5 and W6
    landed, fourteen symbols) is for the GC stream to settle before taking
    it.
14. **Confirmed, kept** (section 4). The hook is generic
    (`gen:1475-1478`, `steer.py:250-298`, the direct call at
    `ffffffff813a1c80`); a `draw` entry passes for the `kworker` class
    (`steer.py:310-311`); the E design's sentence and the comment at
    `Receive.lean:184-188` are corrected in the build.
15. **Confirmed, kept, in this build** (section 3.5). The two-table fix,
    `l_delete_ratelimited6` failing before and passing after, and
    `l_recreate_ratelimited6`; the docstring at `Device.lean:138`.
16. **Fixed** (section 10). The frames list is complete on all three
    trees, the `runner_uniqueness`/`runner_floor` and carried `S1`
    statement edits named as statement edits, main's import closure
    traced (`lakefile.toml:10-11`), and the repair costed at about 1.75
    days across the trees as follow-ons.
17. **Fixed.** The site lines are the file's (`Defs.lean:1209` site 6,
    `:1290` site 124, `:1328` site 130, `:1332-1333` sites 132-133; the
    first version listed the lines in the wrong order against the sites;
    the review's own "124 at :1209, 6 at :1208" does not match the file
    either, which `grep -n '⟨124, \|⟨6, ' Leanux/Kernel/Defs.lean` shows);
    `Device.lean` ranges corrected (`:115-129`, `:128`, `:144-161`,
    `:152-158`); thirteen flood traces plus the control.
18. **Fixed** (section 2.3). A section between two items' records
    mismatches (`Env.lean:887-893`), stated as the fail-closed behaviour;
    the flood wrapper adds the handshake queue and the counter to
    `afterBatch`'s drain check (`:881-882`).
19. **Fixed** (section 3.4). R7, R8, the arm-record attribution and the
    firing tick added to the B3 interface, for the GC stream's use.
20. **Fixed** (section 12). The estimate covers questions 1 and 3 plus
    the uninit fix: about 2.25 days, no oracle rebuild; the GC's 3 to 5
    days are the GC stream's; the proof repair is costed separately.
21. **Fixed** (section 13). U1 names the rule change and the control
    decision; U2 is withdrawn with the GC (and the "closes an instrument
    gap" wording with it); U3's content goes to the GC stream.
