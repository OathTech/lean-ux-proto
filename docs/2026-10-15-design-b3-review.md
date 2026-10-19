# Review of the B3 design (the timer wheel as a mirror) — 2026-10-15

Reviewer: an independent agent [AGENT, reviewer]. Subject:
`docs/2026-10-15-design-b3-timer-wheel.md` at `64f5dbf` (branch
`task/design-b3`, from `ca6b22e`). Read-only throughout: no guest boots, no
check runs, nothing built. Sources read: `kernel/time/timer.c`,
`kernel/softirq.c`, `include/linux/interrupt.h`, `kernel/time/tick-common.c`,
`drivers/net/wireguard/{timers,receive}.c` in `.deps/linux` (6.12.110);
`kernel/config-x86_64-net-choice`; `kernel/patches/gen-choice-stream.py`;
`Leanux/WG/State.lean`, `Leanux/Env.lean`, `Leanux/Kernel/Defs.lean`,
`Leanux/Syscalls.lean`; `docs/2026-10-05-d3-timers.md`; the D3 corpus and
`scripts/wg-d3-controls.py`; `evaluator/check.py`, `evaluator/generate.py`;
`proofs/campaign` and `proofs/campaign-2` through `git show`.

## What holds

Checked against the C and found right: the constants and thresholds
(`LVL_START` = 63, 504, 4032, 32256, 258048; `LVL_DEPTH 9` at HZ 250,
`timer.c:153-188`); `calc_index` rounding up, so a timer fires in
`(expires, expires + 8^lvl]` (`:567-582`); the widths in section 1.4 (level 2
= 64 ticks = 256 ms, level 4 = 4096 ticks = 16.4 s) and the level of every
WireGuard delay at zero lag; one base (`NR_BASES 1`, no `NO_HZ_COMMON`, no
SMP, HZ 250, `PREEMPT_NONE`); `__mod_timer`'s three paths and their line
numbers (`:1085-1088`, `:1115-1130`, `:1144`, `:1173`, `:1180-1183`);
`hlist_add_head` at `:659`; `collect_expired_timers` walking levels while the
low bits are zero (`:1854-1878`), so a level-`l` bucket with expiry `B`
(a multiple of `8^l`) is collected exactly at the step `clk = B`;
`expire_timers` running from the list head with `detach_timer(timer, true)`
(`:1829`); `while (levels--)` running the highest collected level first
(`:2419-2420`); the enqueue-time bucket expiry being the slot's next visit
(the `LVL_START` "last possible delta" offset prevents aliasing with the
current slot, and `timer_recalc_next_expiry` adjusts the per-level clock,
`:1904-1970`); `run_local_timers` raising `TIMER_SOFTIRQ` only at a tick and
only if `jiffies >= next_expiry` (`:2462-2508`); the vector order (HI 0,
TIMER 1, NET_TX 2, NET_RX 3, `interrupt.h:557-566`) and `handle_softirqs`
running a snapshot of the pending mask in bit order (`softirq.c:553-583`),
so TIMER precedes NET_RX within one round. The proof-tree count reproduces:
25 files on `proofs/campaign` name the eight functions (my looser regex
counts 590 theorem/lemma declarations in them, against the note's 588), and
6 on `proofs/campaign-2`. The argument of section 3.3 that unmodeled timers
change which steps exist but not when a modeled bucket runs is sound.

The arithmetic and the order are right. The findings are about the rule the
mirror enforces (E1, E2), the record's site, and claims about the clock lag
and the measurement that go further than the evidence.

## Findings

### 1. The same-slot decision needs a clock that the enqueue record does not carry (blocking)

Section 3.2 consumes the recorded `clk` (step 3), computes `idx` from it
(step 4), and only then decides between "same slot, no record" (step 5) and
"re-enqueue, consume the record" (step 6). But the kind-313 record is written
in `enqueue_timer` (`timer.c:655-680`), which the same-slot path never reaches
(`:1123-1130` jumps to `out_unlock`). On a pending re-arm the mirror
therefore has no `clk` when it has to decide, and the only way to learn the
C's choice is whether a 313 record comes next. That is the mirror following
the record on a C decision (`idx == timer_get_idx(timer)`, `:1123`), which is
exactly what the thin-layer rule forbids. The clock matters here: `idx`
depends on `clk` through the level, so a lag can turn "same slot" into
"move". For WireGuard's delays that happens at the 2 s persistent keepalive
(500 ticks, 4 below `LVL_START(2)`, section 1.4); the circularity is in the
specification for every pending re-arm, though.

Settle: record the base clock where the C reads it, not where it enqueues.
That means a record `{base->clk}` for an armed function after
`forward_timer_base` on both paths of `__mod_timer` (`:1107`/`:1115` pending,
`:1141` not pending; `:1167` is the cross-base path and unreachable on one
CPU). An optional second record `{idx, bucket_expiry}` at `enqueue_timer` can
stay as the arithmetic check. The alternative is a fail-closed rule with no
new site: decide with `clk` ranging over its admissible interval, and treat
the arm as `unsupported` when the same-slot outcome depends on where in that
interval `clk` falls. Either way, U2 should be put to the user with the site
that actually supplies the input.

### 2. E1 as written is one pass at `J_end`, but a wait can contain several ticks (blocking)

Section 3.3 runs `runTimerPass J_end` and says that any next record other
than the pass's next timer section is a hidden mismatch. Section 3.4 then
runs the callbacks' work "as today". In the C, every tick during a wait runs
its own pass, and the work the callbacks queued (send worker, crypt workers,
loopback NET_RX) runs between those passes. So the stream can be
`T(B1) W N T(B2) W N` when `B1` and `B2` become due at different ticks of
one wait. Today's `runTimers` (`Env.lean:406-442`) accepts that interleaving.
E1 as drawn would report a hidden mismatch, which is a false failure. E1 also
says nothing about a timer that this tail work arms or deletes. Examples:
the transmit worker's `wg_timers_any_authenticated_packet_sent` deleting the
keepalive (`timers.c:170`), or the traversal re-arm of a 1 s persistent
keepalive whose bucket falls before `J_end`. The C runs such a timer in a
later pass of the same wait; under E1 it is due at `J_end` but outside the
one pass. The measurement saw no such operation (its five multi-firing
operations are all timers first), so section 5 neither tests this nor rules
it out. It is reachable whenever two buckets fall less than one wait apart,
for example a generated advance whose 25-tick wait reaches a second timer's
bucket.

Settle: state E1 as a sequence of passes whose boundaries the section
stream places (the environment's tick placement, as section 3.4 already says)
and which the wheel constrains:
- the next timer section is always the earliest pending modeled bucket
  (level descending, list head first);
- a boundary (a non-timer record) may come after step `B` only when no other
  pending modeled timer has bucket expiry `B` (a step is never split);
- work between passes runs in record order and may arm or delete;
- at the kind-310 read, no pending modeled bucket is `<= J_end`.

The only freedom left is the unrecorded tick `J_i ∈ [B_i, B_{i+1})`. Add a
unit test and, if one can be generated, a trace with two passes in one wait.

### 3. After an advance, E1 must wait for the absorbing tick; as written the timer control changes its failure (should-fix)

Section 3.4 justifies `J_end` by "a tick between the last pass and the read
would have run another pass". `wg_advance` moves `jiffies` without a tick
(`leanux_time_advance` → `do_timer(ticks)` with interrupts off,
`gen-choice-stream.py:975-1003`), and no `TIMER_SOFTIRQ` is raised until the
next real tick (`run_local_timers`, `timer.c:2502-2504`). In the normal guest
the polling wait guarantees that absorbing tick (D3 section 13, "the first
arm record after each advance has `jiffies = after + 1`"). The control
`tc_advance_wait0` removes the wait on purpose. There `J_end` can equal the
advance's `after` value, E1 demands that the made-due keepalive has fired,
it has not, and E2 makes the advance operation `unsupported`. That is not one
of the control's accepted failures (`{'hidden_mismatch', 'dispatch sections
opened but not recorded'}`, `scripts/wg-d3-controls.py`), so section 6's
"still fails in its stated way" does not follow.

Settle: in E1, a pass has run at the advance's jump only if `J_end > after`
(a tick followed the jump); with `J_end = after`, nothing made due by the
jump has fired yet, and the section then lands in the next operation as
today. Re-derive section 6's control claim from that.

### 4. E2 is not exact, and its trigger is misdescribed (should-fix; bears on U4)

E2 turns every "due timer without its section before the read" into
`unsupported`. A must-fire violation has two sources: the kernel deferring to
ksoftirqd, or the mirror's wheel predicting a bucket too early (wrong level,
wrong rounding, a deletion it missed). E2 labels both `unsupported`. At check
time that still fails the trace (`ModelStopped`, `evaluator/check.py:305-307`),
so it is not silent. But it is mislabelled: a mirror defect reported as an
environment outcome, in the one direction E1 adds. The trigger is also
narrower in the note than in the C. `MAX_SOFTIRQ_TIME` is
`msecs_to_jiffies(2)`, which is one jiffy at HZ 250 (`softirq.c:500`). So
`time_before(jiffies, end)` fails as soon as any tick lands during a round.
`need_resched()` also defers (`:598-602`), and it is commonly set when a
callback wakes a kworker from the idle task. "Exhausted its 2 ms or 10
rounds" undersells how the deferral arises on this configuration.

Settle: make E2 exact by lookahead. Report `unsupported` only when the
missing timer's section does appear later in the stream, after the read (in
the same operation's remainder or the next operation), and report a hidden
mismatch when it never appears. Correct the trigger text. With that, U4 is a
sound environment boundary. Without it, U4 makes the new direction fail with
the wrong label.

### 5. The clock lag is larger and two-sided; the "one place" and "a level up" claims are wrong in general (should-fix)

Section 1.2 says `clk` lags `jiffies` "exactly when a timer … is due and its
softirq has not run". Two corrections:
- `clk` also leads `jiffies` by one after a pass whose last step was at the
  current tick (`base->clk++`, `:2416`; the struct comment at `:226-228`).
  Every arm until the next tick then sees `delta = delay − 1`. No WireGuard
  delay sits on a threshold, so no level changes, but this, and not only "the
  forward reads `jiffies` once more", is why the bound `clk <= J_m + 1`
  holds.
- Inside a catch-up pass after an advance, a callback's arm runs with
  `clk = B + 1`. The forward then moves `clk` only to the next due bucket of
  any owner (`:1008-1014`), so it can lag `jiffies` by up to the advance.
  `wg_expired_send_keepalive`'s `need_another_keepalive` re-arm (+2500,
  `timers.c:84-88`) and the give-up's zero-key arm (`:60-62`) are such arms.
  After a large advance the keepalive re-arm's `delta` can reach level 3 or
  4, not 2.

So "the one place in the corpus where the lag changes the bucket width"
(section 1.4) is a fact about this corpus, not about the reachable domain.
Section 11.4's "the generator's margins already cover a level up" does not
cover two levels. Section 5's "zero observed level changes" reflects the
absence of such re-arms in the corpus. This strengthens the case for
recording the clock, but the note should say so.

The checks of step 3 are also weaker than the mirror can make them. When a
modeled bucket `B <= J_m` is pending (overdue), `clk <= B` is computable and
should be checked. Otherwise `clk ∈ {J_m, J_m + 1}` or `clk = prev_pass_end`.

Settle: correct section 1.2's statement, section 1.4's last paragraph and
section 11.4. Add a generated or corpus trace with a keepalive re-arm inside
a catch-up pass (data received while the keepalive is pending, then a long
advance). Give the clock channel its own one-off mutant (`clk := J_m`),
rejected by that trace.

### 6. Mutant B3-M2 cannot be rejected as specified (should-fix)

`LVL_START(2)` as 512 moves only delays in `[504, 512)` from level 2 to
level 1. The retransmit's delay is 1250 to 1332 (level 2 either way), and no
WireGuard delay falls in `[504, 512)` (persistent keepalive 250·i gives 500
or 750). So `d3_retransmit` does not reject the mutant, and probably nothing
in the corpus does.

Settle: pick a threshold mutant that a real delay crosses. Examples:
`LVL_START(4)` as 135001 (zero-key to level 3, every session trace), or
`LVL_START(2)` as 1300 (retransmit with jitter at least 50 to level 1).

### 7. The state does not say how the pass knows a slot's expiry, nor how it treats callbacks that touch collected siblings (should-fix)

The C stores only `idx` (in `flags`) and derives a slot's due time from
`base->clk` stepping through `next_expiry`. The mirror's `clk` is "the base
clock as last recorded" (section 3.1) and does not step, yet the pass
(section 3.3) needs "the slots at the smallest bucket expiry". The faithful
abstraction is a per-timer bucket expiry. It is set at enqueue, kept
unchanged on the same-slot path (the C keeps the slot, so the old expiry
stands; recomputing from the new `expires` is wrong when the index aliases
one wrap later), and justified by the no-aliasing argument. The note should
state that representation and its invariant.

The pass should also re-scan the live wheel after every callback rather than
snapshot a bucket. `wg_expired_retransmit_handshake`'s give-up deletes the
keepalive (`timers.c:51`), which can share the retransmit's level-2 bucket.
In the C it is detached from the collected list and does not run (`:928-938`).
A collected sibling re-armed into its own slot index stays in the collected
list and does run. A per-timer stored bucket plus a re-scan gives both
outcomes.

Settle: write this into section 3.1 and 3.3. Add a unit test for the give-up
deleting a same-bucket keepalive. Make the pending ↔ slotted invariant a
runtime `invariant` check (fail-noisy) rather than unit tests only, including
"no wheel entry for a released peer id" at `retirePeerUnits` (peer ids
restart on a fresh device, `Defs.lean:1508-1516`).

### 8. The lock-context argument for the hook is wrong (should-fix; bears on U2)

Section 7 says the steering lookup's leaf lock "is already taken under the
timekeeper locks by the kind-304 writer". It is not: kind 304 is written with
`kcov_choice_write` (`gen-choice-stream.py:1000`), which skips steering. A
313 written through `kcov_choice_ip` (as `kcov_timer_arm` does, `:823`)
calls `kcov_steer_find` and `kcov_steer_apply`, taking `kcov_remote_lock`
(in the trace task's own context) and `steer->lock` (`:134-196`) under
`base->lock`, a raw spinlock with interrupts off. That is probably safe
(non-RT, and I found no path holding those locks that arms or deletes a
timer), but the note's reason is not the reason.

Settle: write the record with the mode check and `kcov_choice_write`, with
no steering lookup (nothing should steer it), or state the lock order and
why nothing takes `base->lock` under `kcov_remote_lock`. Also make the record
carry the timer's address (32 bytes instead of 24). Then "resolved by kind"
(section 6) does not lose the site guard: the checker can require each 313
to name the timer of the 303 it follows.

### 9. The measurement is weaker than its summary, and cannot be reproduced (should-fix)

- "Fed only the recorded clocks" is not exact. The handshake-completion
  deletion (`timers.c:194`) was taken from kind-205 records (the
  `ktime_get_real_ts64` in `wg_timers_handshake_complete`, consumer frames
  `receive.c:179`, `:347`). That is a legitimate stand-in for control flow
  the mirror performs, but it is a record of something other than a clock,
  and without it 17 firings mismatched.
- The script counted "a timer predicted due that never fires and is later
  re-armed" as deleted. That rule absorbs exactly the must-fire violations
  E1 introduces. The deletions at `timers.c:170` and `:178` were not
  modelled at all. The note reports two such timers, both explained, but not
  how many predicted-due-not-fired timers there were in total, by
  disposition, nor what happened to those never re-armed. So the 46/46 and
  40/40 figures support the may-fire direction and the order. The must-fire
  direction rests on the two named cases.
- The script was deleted. The global working rules keep the command that
  reproduces a result. Here the conclusion is committed and the command is
  gone.

Settle: either commit the replay script and rerun it reporting every
predicted-due timer with no section, by disposition; or, more cheaply, let
the built B3 mirror settle it with the `wireguard` suite (about 3 minutes),
since the mirror performs all the deletions. Until then, state the summary
as "the may-fire direction and the order, 46/46; the must-fire direction,
no unexplained case among those the script classified".

### 10. The note departs from the plan's B3 line without saying so (should-fix)

The parallel plan's B3 row says the stream makes "the kind-310/311 reads
become derived" (`docs/2026-10-14-wireguard-parallel-plan.md:45`). The note
keeps 310 (with a sound argument), keeps 311 (with no argument), and adds a
record. The user deciding U1 should see that B3 delivers the firing set and
order as semantics but not the derived reads the plan named.

Settle: one sentence in section 0 and in U1.

### 11. "Last armed first within a bucket" is not the C's order (note)

Sections 0 and 1.3 say "last armed first". A same-slot re-arm keeps the list
position (`:1123-1130`), so the order is last *enqueued* first. Section 3.2
step 5 has it right. Fix the summary.

### 12. "Highest level first at one step" has no witness (note)

That order only shows when buckets of different levels have the same expiry
`B` (a multiple of `8^l`). The note's multi-level cases (`d3_zero_key`,
`l_delete_after_clear_work`) are ascending different expiries, not one step.
The mirror will carry an order rule nothing exercises. Say so, or construct a
trace.

### 13. The proof carry is counted right but underestimated (note)

The 25 files are the ones naming the timer functions. The heaviest ones
restate the mirror's code verbatim. `WG/Environment/TimerSource.lean` copies
`fireTimer` and closes it by `rfl`. `WG/Lifetimes/EnvTimersAudit.lean`
carries audit copies of `runTimers`, `fireTimer`, `idleTimers` and
`afterAdvance`, with erasure and preservation theorems. Those are rewritten
against the pass, not re-proved. If `timerBase` becomes a field of `Kernel`,
`Framing/WGKernel.lean`'s `WGKernelView` (referenced by 54 files on
`proofs/campaign`) and every frame naming `Kernel`'s fields also move. One
to two agent-days is optimistic; two to four is more credible. A
representation that keeps the wheel's per-timer data with the timer
(`expires`, slot, stored bucket, an enqueue stamp for list order) would
localise the carry. It is a legitimate alternative to weigh against the
576-slot array, which section 3.1 does not discuss.

### 14. U3 is consistent, but make the boundary explicit (note)

Putting `timer.c`'s control flow in the mirror while leaving it unanchored
is consistent: the level choice and rounding are checked by the record's
`idx` and `bucket_expiry`, which is stronger than a branch witness. The two
early exits are witnessed only by a record's absence, and they have the same
effect, so the difference is unobservable. Two loose ends:
- the declared boundary should name `timer.c` as mirrored but unanchored, so
  a reader of `correspondence/kcov.json` or `docs/proofs.md` knows;
- the `timer.c` hooks are not line-preserving (the existing ones add lines,
  `gen-choice-stream.py:1172-1201`). That is fine while the file is
  unanchored, and U3's choice is coupled to it.

### 15. The estimate is plausible for the build as written, short once 1–9 land (note)

The 4 agent-days break down plausibly. Closing findings 1, 2, 3, 4 and 7 (a
second hook site or the fail-closed rule, the multi-pass rule, E2's
lookahead, the representation) and adding the traces of 2 and 5 adds about a
day or two. Five to six agent-days for the build is my estimate; the carry is
separate (finding 13).

### 16. Lane E's gain is real but narrower than worded (note)

What B3 buys for key lifetime is the must-fire direction. In every run the
mirror accepts, the zero-key callback has run by the first idle read with
`J_end >=` its bucket expiry, and its clear work has been queued. Today that
statement cannot be made, because the mirror accepts a run in which a due
timer did not fire. The bound is over accepted runs (E2 and mid-body ticks
excluded) and depends on the recorded `clk`. After finding 5 that includes
level 5 (width 32768) in a catch-up pass long enough. The note's "the C's
bound … `+ 8^lvl`" is right with `lvl` computed from the recorded clock;
"level 4" is the zero-lag case only.

## Verdict

**Build with the named changes.** The wheel's arithmetic, the expiry order
and the softirq order are what the C does. The record is needed: the clock
lag depends on timers outside the modeled set and, inside catch-up passes,
can cross levels. The measurement is real evidence for the may-fire
direction and the order. Two things must change in the note before the user
decides U1 and U2:
- the record must sit where the C reads the clock, so that the mirror
  computes the same-slot decision instead of reading it off the record's
  presence (finding 1);
- E1 must be restated as passes bounded by the stream, so that it is exact
  for waits with several ticks and for work that arms or deletes between
  passes (finding 2).

Findings 3 to 10 should be fixed in the note or the build: the absorbing
tick, E2 by lookahead, the lag claims and a trace and mutant for the clock
channel, a rejectable B3-M2, the representation, the lock argument, the
measurement's wording and script, and the plan departure. None of them calls
for a redesign.

## For the user: the environment-line move (U1)

The move makes "which WireGuard timers fired, and in what order" something
the mirror predicts from the C's wheel and checks against the kernel, where
today it is read from the records. It also closes today's silent direction:
a due timer that did not fire is currently never reported by the mirror, and
under E1 it is. That is the real gain. It is also what a key-lifetime result
over the mirror needs.

The risks:
- More traces may stop as `unsupported` when the kernel defers its timer
  softirq to ksoftirqd (one tick landing in a busy softirq round is enough
  at HZ 250). The s4 run saw none in 1312 waits, but it is load-dependent.
- The rule as drafted is too strict for waits that contain more than one
  timer tick, and as drafted it would read the record's presence to decide
  one C branch. Both are fixable, and both fixes are named above.
- A heavier proof carry than estimated.

I would take the move once findings 1 and 2 are folded into the note. Its
two directions would then be exact. The environment would still own only
what no model of the code can know: when the ticks landed, how many ticks a
wait took, and the base clock's lag. I would also make U4 conditional on
E2's lookahead (finding 4), so that a mirror mistake can never pass as a
host-timing outcome.
