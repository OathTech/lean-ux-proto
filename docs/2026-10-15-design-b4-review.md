# Design B4 review: load, the ratelimiter's GC, the entry allocation — 2026-10-15

Independent review of `docs/2026-10-15-design-b4-load-ratelimiter.md` at
0691477 (branch `task/design-b4`, from main ca6b22e) [AGENT, reviewer].
Everything here was read, not run: no guest boot, no check. The kernel build
inspected is the s4 oracle in the main checkout
(`.artifacts/kernel-net-choice-s4`: `System.map`, `objdump` of `vmlinux`).
Where a claim needs a run, the finding says which run settles it.

Severity: **blocking** (must change before the design is built or put to the
user as written), **should-fix** (change in the design or the build),
**note** (correct the text, or a confirmation).

## Findings

### 1. Blocking: the section 2.4 measurement does not measure the proposed design

The note presents the exact-versus-summarised table as evidence for U1 ("the
exact execution consumes the same 1,565 remote records the summary discards
or folds", "5,703 branches", "agreement"). The run used `LEANUX_FLOOD_EXACT=1`,
and that path is not the design:

- `Env.flood` calls `discardFloodRecords startW cuts` (`Leanux/Env.lean:812`)
  *before* the `floodExact` branch (`:821`). In the exact run the 520 producer
  sections and the queue record (520 + 520 + 1 = 1,041 of the 1,565 records)
  were still discarded, not consumed by a producer. The worker consumed 524.
  The producer side through `Env.batch`, which is the substance of
  section 2.3, never ran.
- The exact branch still sets `handshakeQueueLen` to the batch's size before
  the worker (`:828`), so "the batch-before-worker fact becomes what the
  records show" was not exercised either.
- The checker's `wg_flood` arm (`evaluator/check.py:1043-1059`) skipped
  `control_flow` for the flood in both runs. "Agreement, 7 operations" says
  nothing about the 5,703 branches against coverage. Finding 2 shows that,
  with the arm deleted and nothing else changed, the checker would reject
  them.
- "1,565, the same" is the kernel's record count, fixed by the kernel. It is
  the same whatever the mirror does, so it is not evidence of consumption.
- The row label "520 clock reads (`:115`)" is wrong. With 520 packets queued,
  the counter is at least 512 for the first 9 packets only (site 130,
  `receive.c:115`). The other 511 take the decay read (site 6, `:117`). The
  table's own operand figure agrees: 1,049 pairs = 520 `hsUnderLoad` + 511
  `hsDecayExpired` + 18.
- The 10 ms cost covers the worker half only. The "about 8,000 labels" with
  producers is an estimate.

**Settle:** prototype `Env.flood` over `Env.batch` with the checker changes
of finding 2, run the thirteen `corpus/wireguard` flood traces and the
control (`check.py --suite wireguard` on those ids), and restate the table
from that run before U1 goes to the user.

### 2. Should-fix: deleting the checker's flood arm is not enough; the needed checker changes belong in U1

Without the arm, the flood goes through the ordinary `control_flow` rules:

- "decision reported more than once" applies to every decision not declared
  `repeatable`. Only `wg_batch` and `wg_netns_close` are exempt
  (`check.py:1097-1106`).
- "opposite outcome covered" applies unless the decision is `repeatable`
  (`check.py:1133-1140`).

`hsUnderLoad` (true for the first 9 packets, false after), `hsWasUnderLoad`,
`hsDecayExpired`, `macInvalid`, `macNoCookieCheck`, the `packet_needs_cookie`
arms, `rxHandshake`, `rxQueueBusy` and `rxProduceFailed` are all
non-repeatable (`Leanux/Kernel/Decision.lean:2959-3060`). So every flood
would fail. The flood also needs the batch's file restriction (`op_files =
BATCH_FILES`, `check.py:1066`): its `io_uring_enter` runs the same fixture
plumbing in `fs/file.c` that `wg_batch` excludes.

The fix is a checker rule change on the trust surface: the op exemption, and
either `repeatable` declarations (which apply in every operation, not only
floods) or a per-operation repeat rule. Under it, the per-packet reports
collapse into outcome sets. Per-packet precision then rests on the record
stream (each tail packet's clock record consumed in order at its exact site:
this part is exact) and on the operand rows (one-directional, finding 3). It
does not rest on control flow. "The flood's decisions are checked like any
operation's" overstates this. U1 should name the rule change and what it
weakens.

### 3. Note: the operand instrument is one-directional (section 2.2)

"520 distinct rows, each of which a mirror `branchCmp` must match
(`operand_rows_distinct`)" is not how the check works. `operand_agreement`
checks each *mirror* obligation against some kernel row. Surplus kernel rows
need no counterpart (`check.py` docstring at `:1243-1246`, the pre-release
review's finding 5). `operand_rows_distinct` is a report counter
(`:1857`, `:1908`), not a check. The conclusion, no new record kind for a
derived counter, still holds. The per-packet completeness argument should
rest on the in-order clock records, which are exact, not on the rows.

### 4. Should-fix: the trylock arm (section 2.5) uses the wrong threshold and the wrong lock

- The busy test is `> MAX_QUEUED_INCOMING_HANDSHAKES / 2` = 2,048
  (`messages.h:51`; the mirror has it right at `Receive.lean:473`; the
  E design's section 11 says "more than 2048"). It is not 1,024. A flood of
  1,100 (`e_underload_busy`) never takes the arm. The k-th produce sees k-1
  queued, so the smallest batch that takes the arm once is 2,050.
- The argument names the wrong lock. The worker consumes under
  `consumer_lock` (`ptr_ring_consume_bh`, `include/linux/ptr_ring.h:365`).
  The trylock is on `producer_lock` (`receive.c:555`), which only producers
  take (`ptr_ring.h:162`). The worker's position is irrelevant.
- The conclusion is right for a simpler reason: on this configuration the
  trylock is constant. `CONFIG_SMP` and `CONFIG_DEBUG_SPINLOCK` are off
  (`kernel/config-x86_64-net-choice`), so `arch_spin_trylock` is
  `({ barrier(); (void)(lock); 1; })` (`include/linux/spinlock_up.h:56`).

Record that argument, keyed to the configuration, and size the trace at
2,050 or more. It fits the branch bound (about 11 labels per packet on the
worker, finding 1).

### 5. Note: the E sentinels the note relies on do not exist

"The sentinel set does not change: E-M8 … covered by the exact execution …,
E-M10/M11 by the ratelimit traces" refers to the catalogue that was rewritten
on 2026-10-12. `scripts/wg-mutants.py` has thirteen sentinels and none for E
(`:36-121`). Either claim nothing, or add a one-off mutant for the exact flood
(for example, the threshold at 511), rejected by `e_underload_511/512/513`.

### 6. Should-fix: keep the merged-injection control; drop the miscount control

`e_underload_miscounted` would need a seam that feeds the mirror an input
different from the guest's. None exists: `scripts/steering-controls.py` runs
corpus traces through `evaluator.check` unchanged. A seam like that in the
check path is a back door, and it is not needed: the existing control already
tests the exact execution. The Runner ignores `control` (`Runner.lean:646-650`),
so the kernel processes a valid initiation the mirror does not model, and the
run diverges at the first cookie record and at the counter's operand. Keep
`e_underload_merged` and update its expected detail.

The proposed positive trace `e_underload_control_valid` adds nothing. The
guest puts the control right after the leading valids (`guest.c:1588-1593`),
which is exactly an extra leading valid: that is `e_underload_two_replies`.

This answers the C1 question. The summary and the section discard existed
because a site-level skip of site 6 would eat the injection's own record
(E design 4.1, C1). The exact execution has no skip at all: every record is
consumed at its own site, in order. An operation's records end at the
operation, and `requireDrained` stops a worker that outlives the wait. A
merged or extra packet diverges the per-packet sequence. The guard is kept,
and made stronger, provided findings 2 and 18 are applied.

### 7. Should-fix: the arm hook at `__queue_delayed_work` does not attribute to `ratelimiter.c:81`/`:191`

`__queue_delayed_work` is out of line in the oracle build (`System.map`:
`ffffffff81090570 t __queue_delayed_work`; `queue_delayed_work_on` calls it at
`ffffffff81091751`). `_RET_IP_` inside it is therefore an address in
`queue_delayed_work_on` (`kernel/workqueue.c`), the same for the init's arm
and the requeue. "Two sites of kind 303 beside the peers' arm site" will not
come out of the hook as specified. It stays record-only if redesigned. Either:

- pass the outer return address from `queue_delayed_work_on` and
  `mod_delayed_work_on` (both exported; the WireGuard callers inline
  `queue_delayed_work`) into the hook; or
- declare one `workqueue.c` site and distinguish the two arms by mirror
  state.

The section 1.3 line numbers are off by one to three: `timer->expires` is at
`:2548`, `add_timer_on` at `:2555`/`:2560`, `add_timer_global` at `:2558`.
The note also leaves out `clear_pending_if_disabled` (`:2586`), which
finding 8 needs.

### 8. Blocking (GC): the cancel model is wrong for 6.12

`cancel_delayed_work_sync` is `__cancel_work_sync(…, WORK_CANCEL_DELAYED)`,
which passes `WORK_CANCEL_DISABLE` (`workqueue.c:4386`) and re-enables only
after `__flush_work` (`:4400-4401`). While the work is disabled,
`queue_delayed_work_on` sets PENDING and then `clear_pending_if_disabled`
(`:2585-2586`, `:2386-2399`) clears it again without queueing. So the
requeue inside a run that the cancel is waiting for arms nothing, and writes
no 303 record (the hook is below that test).

The note says that requeue "arms a timer that the cancel then deletes". On
every `wg_delete` that meets a GC run in progress, the mirror would expect an
arm record that never comes. The state needs the disable count (a
`gcDisabled` flag across the cancel), and the arming rule needs the
`clear_pending_if_disabled` test.

### 9. Blocking (GC): the inter-operation gap is loud, not silent; the proposed fix leaves the trace's head and tail open and ignores capacity

**Not silent.** `section_problems` (`check.py:653-667`, since 0437dbc,
2026-10-04) compares the kernel's opened-section count, which the guest
reads after the trace (`guest.c:1479-1484`), with the section starts
recorded across all operations. A section lost between one operation's read
and the next operation's reset fails the trace with "dispatch sections opened
but not recorded".

- The per-operation reset dates from b87df92 (2026-10-01), and the
  `wg_observe` exception from e179093 (2026-10-06).
- Remote coverage and records exist only inside sections, so since sections
  exist the gap has not been able to hide anything silently.
- The integration record must **not** carry this as a found instrument gap.

"No peer timer lands there: their delays (5 s and up)" is also inaccurate:
`d3_persistent_keepalive` uses a 2 s keepalive. Its natural firings land in
the `wg_observe` waits by design, and `section_problems` covers it if one did
not.

**What it does mean for B4.** Once the GC is armed in a trace, a firing in
any window outside an operation's reset-to-read span becomes a frequent loud
failure. The gap rule must close every such window. As written it closes
only the windows *between* operations:

- **The tail.** After the last operation's read, the trace child runs
  `delete_wg0` (`guest.c:2727`, `:2755`), whose `cancel_delayed_work_sync`
  comes last. A firing between the read and the cancel is opened but never
  recorded. A rule is needed, for example a final drain attributed to a
  trailing idle segment that the mirror consumes.
- **The head.** Records written before operation 0 (after the dispatch load)
  must be stated to belong to operation 0.
- **Capacity.** Never resetting means the remote area holds every remote
  record of the trace. `CAPACITY` is 4 Mi words (`guest.c:51`), the
  comparison child's records are 4 words each, and `full_remote_kcov`
  (`:2676`) would then trip on the cumulative count. A trace with a large
  batch, a large flood or several `wg_create` windows needs numbers.

**The mutant does not work as described.** `gc_work` is static, so the
timer and work addresses never change: "the next arm names an unknown unit"
cannot happen. The GC's phase relative to the operations is also
uncontrolled, so "a trace whose GC fires in a gap" cannot be placed
deterministically. What would reject the reset-keeping guest is
`section_problems`, and only on runs where a firing happens to land in a
gap.

**Settle:** one guest run measuring, per WireGuard trace, the wall time
outside the reset-to-read spans (the gaps plus the tail). That gives the
failure rate a GC armed everywhere would cause under today's guest.

### 10. Should-fix (GC): "never predicted" detects no missing firing

The rule in section 3.5 consumes GC sections where the records place them.
No rule rejects a firing that should have happened and is absent: the timer
and work units are constant, and a stale `gcTimer` passes the next firing's
due test. The peer timers have the same property today: `runTimers`
(`Env.lean:406-441`) consumes only the sections present. So a missing GC run
is caught only by `section_problems`, if it was opened, or later by the
site-132/133 divergence, if entries existed.

Add a completeness rule wherever the mirror knows `jiffies` (kind-310 reads,
303 arms, 311 reads): a pending GC timer that was due by then must already
have fired. It has to respect the wheel. `calc_index` rounds the expiry up
(`timer.c:579-580`), and with a delay of 250 the timer sits on level 1
(`LVL_START(1)` = 63, granularity 8), so it fires in `(E, E+8]`. The rule
must also either argue away a softirq deferred to `ksoftirqd` or state it as
a residual. If it cannot be made exact, state the limit. The strict due test
the note gives (`time_before(expires, J)`) is sound, because of that same
rounding up, which is the reason to cite.

### 11. Should-fix (GC): case (ii) is common, and the GC is armed in every WireGuard trace

- A tick's `TIMER_SOFTIRQ` runs before `NET_RX` in the same
  `handle_softirqs` pass. That includes the `local_bh_enable` of every
  loopback send inside the trace task's system call, so nested GC firings
  are not rare: their rate is the fraction of time spent in task sections and
  system calls, times about four firings per trace.
- Rule (ii)'s claim that the run follows "at the task's next yield … for the
  trace task its return to user mode" is not right. The trace task's yields
  are unrecorded: `kcov_dispatch_resched` writes only inside a dispatch
  section (`gen-choice-stream.py:586-600`). A sleep or `cond_resched` inside
  a system call (for example `__flush_work`) runs the GC's run in the middle
  of the call. Its placement then rests on sequence order alone.
- Arming `wg_ratelimiter_gc_entries` in every WireGuard trace makes every
  WireGuard verdict depend on the new placement rules. Arm it per trace
  (`harness/linux.py:106-127`, as `cleanup_net` is armed) in the GC traces
  only, and leave the rest under the stated exclusion.
- The first-day spike should also measure how often case (ii) occurs over the
  full WireGuard suite, not only on `e_underload_ratelimit_gc`.

### 12. Should-fix (GC): the activation machinery does not cover the GC's walk

`Activation` is defined for queue-draining workers (`Env/Batch.lean:141-152`,
`201-227`: "not a draining worker" invariants elsewhere). A 2,048-bucket walk
with a resched point per bucket, resumable after a yield, is a new activation
kind with its own fuel and consistency test. The design and the estimate
should carry it.

### 13. Note: dispatch slot 14 is reserved

`Defs.lean:950-956` reserves indices 14-15 for "W5-W6's two units". The GC
taking index 14 conflicts unless those reservations are dead. Say which, and
update the comment.

### 14. Note, confirmed: the kind-305 hook is generic, and the E design's sentence is wrong

- `__kcov_alloc_pre` tests `canonicalize_ip(addr)` against the loaded ranges
  (`gen-choice-stream.py:1475-1478`).
- The ranges come from `ALLOC_SITES` rows through `objdump`
  (`harness/steer.py:250-298`).
- `wg_ratelimiter_allow` calls `kmem_cache_alloc_noprof` directly
  (`ffffffff813a1c80` in the oracle).
- A `draw` entry is accepted for the `kworker` class (`alloc_refusal`
  returns before the class gate, `steer.py:310-311`).

The E design's section 11 sentence and the comment at `Receive.lean:184-188`
are wrong, as the note says.

### 15. Note, confirmed: the two-table uninit defect is real

- `gcEntries false` empties `table` only and reports `gcV6EntryIter` false
  (`Leanux/WG/Device.lean:152-158`).
- `ratelimiterInit` resets `table` only (`:127`), whereas the C walks both
  tables (`ratelimiter.c:64-74`).

It could not have hidden a wrong verdict silently:

- A delete with IPv6 entries would make the kernel cover `:73` while the
  mirror reports `gcV6EntryIter=0`, which is "opposite outcome covered".
- A re-create followed by a lookup from the same `/64` would give site 132
  against 133.

No corpus trace has IPv6 entries followed by `wg_delete`
(`l_delete_ratelimited` is IPv4). The fix and the `l_recreate_ratelimited6`
witness are right; `l_delete_ratelimited6` should fail before the fix. The
`gcEntries` docstring ("an IPv6 handshake is `unsupported`") is stale too.
This fix is independent of the GC and can land with questions 1 and 3.

### 16. Should-fix: the frames list is incomplete, and some of it is statement edits

**Statement edits.** Deleting `floodExact` changes `Runner.executeTrace`'s
signature. On `proofs/campaign` these quantify over it:

- `WG/AntiReplay/Statements.lean:29-41` (`runner_uniqueness`,
  `runner_floor`): an edit to a register result's statement, to be named as
  such under Rule Zero;
- `Logged/Runner.lean:12-122` and `Logged/Checkpoints.lean:41-154`;
- `WG/Keypairs/Evolution/{Bounds,Runner,Syscalls}.lean`.

**Proof re-runs and re-mirroring, also missing:**

- `proofs/campaign`: `Logged/Operations.lean:291-350` (its own `floodLogged`
  copy; the note cites only campaign-2's) and
  `WG/Lifetimes/EnvTrafficAudit.lean:85,99` (the flood's state updates);
- `proofs/campaign-2`: `WG/Keypairs/Evolution/Operations.lean:41-43,119`
  (`floodLogged_evolves`, and the `discardFloodRecords`/`floodTailEffect`
  frames it uses);
- `packetReceive_ordinary` (`WGMore.lean:460`, both branches) for the busy
  arm;
- `Keypairs/Frames/WGDevice.lean:53-64` (`ratelimiterInit_`/`gcEntries_`
  snapshots).

On main, the only result in `LeanuxProofs` is ReplayWindow. The stale
`Leanux/Proofs/Logged/Operations.lean` there is outside the build and not
affected.

### 17. Note: citation drift

The `Defs.lean` site lines are one low (124 is at `:1209`, 6 at `:1208`),
and `Device.lean`'s ranges are shifted. The corpus holds thirteen flood
traces in `corpus/wireguard` plus the control, not fourteen.

### 18. Note: two `Env.batch` details

- "If a run ever had the worker preempt the submitter … the exact execution
  would follow the records anyway" is not what `Env.batch` does. A section
  between two items' records mismatches (`Env.lean:887-893`), which is the
  right fail-closed behaviour; say that.
- `afterBatch`'s `requireDrained` (`Env.lean:881-882`) omits the handshake
  queue. The flood wrapper must add it, as section 6 intends.

### 19. Should-fix: the B3 interface (section 3.7) is not sufficient

R1-R6 are right as far as they go. Missing:

- **R7, completeness:** a due timer must have fired by any known `jiffies`
  (finding 10).
- **R8, the disable state** during `cancel_delayed_work_sync` (finding 8).
- **Arm-record attribution** (finding 7).
- **Firing tick:** a wheel model must place the GC timer by `calc_wheel_index`
  like the peers' (level 1, granularity 8, firing in `(E, E+8]`); the
  deferrable flag is not the only thing to state.

### 20. Should-fix: the estimate

- **Questions 1 and 3 and the uninit fix:** about 2 to 2.5 days, which is
  credible once the checker changes (finding 2), the 2,050-packet trace
  (finding 4), the kept control (finding 6) and the campaign lag items
  (finding 16) are counted.
- **The GC:** 1 to 1.5 days is not credible. It carries findings 7 to 12:
  hook redesign, kernel rebuild and new identity, the guest's window and
  tail rule with capacity numbers, the disable model, a new activation kind,
  the nested-section rule (the stop risk) and its suite-wide spike, and
  per-trace arming. Count 3 to 5 days plus the claim-point check.

So 0.15 WU for all of B4 is optimistic. The parallel plan's row budgeted
2 days of build.

### 21. Should-fix: the user decisions in section 13

- **U1** must name the checker rule change (finding 2) and the control
  decision (finding 6). As written it describes a deletion, but the change
  also adds a weaker set-semantics rule for the flood's decisions.
- **U2:**
  - must drop "closes an instrument gap" (finding 9);
  - must add the choice between arming the GC in all WireGuard traces and in
    the GC traces only (finding 11);
  - must state the head, tail and capacity rule of the guest change.

  The two hook changes are record-only and class-approved: they open
  sections and write records only for armed functions, and no armed work
  function is a delayed work today. `linkwatch_event` is one, but no trace
  arms it (`linux.py:106-127`); W8b will inherit the new firing sections and
  arm records when it does. Listing the hooks under U2 is a courtesy, not a
  requirement.
- **U3** as a stop condition is fine.
- **The tactical list** is fine except the trylock argument (finding 4).

## Answers to the brief's questions, in one line each

- **C lines:** `receive.c`, `ratelimiter.c` and `cookie.c` say what the note
  says. The `workqueue.c` line numbers are off by one to three, and the
  `cancel_delayed_work_sync` semantics are wrong (finding 8).
- **Exact flood:** sound, and stronger than the summary, including against
  C1. It is not yet measured (finding 1), and it needs checker changes
  (finding 2) and the kept control (finding 6).
- **The kind-305 hook:** generic, as claimed (finding 14).
- **The GC's oracle changes:** record-only, yes. The arm hook's attribution
  fails as specified (finding 7). The guest change alters no remote row of a
  run that passes today, since anything in a gap already fails it, but it
  leaves the tail open and has a capacity cost (finding 9).
- **The gap:** real since 2026-10-01, loud since 2026-10-04, hid nothing
  silently. It does not belong in the integration record as a found gap
  (finding 9).
- **The nesting:** not handled. It is the stop risk the note says, larger
  than stated, and best contained by per-trace arming (finding 11).
- **The uninit defect:** real, fail-closed, unexercised; the fix is right
  (finding 15).
- **The B3 interface:** insufficient without R7, R8, the attribution and the
  firing tick (finding 19).
- **The measurement table:** does not support the claims (finding 1).
- **The frames list:** incomplete, and it includes statement edits
  (finding 16).
- **U1 to U3:** classified correctly, but U1 and U2 are incomplete or
  misframed (finding 21).
- **0.15 WU:** credible for questions 1 and 3 only (finding 20).

## Verdict: build with the named changes; questions 1 and 3 now, the GC after a redesign

Build questions 1 and 3 and the two-table uninit fix, with findings 1 to 6,
15, 16 and 18 applied:

- re-measure with the real `Env.batch` path and the checker changes before
  U1 goes to the user;
- name the checker rule change in U1;
- size the busy trace at 2,050 or more, with the configuration argument;
- keep `e_underload_merged`;
- complete the frames list.

That part is sound. Retiring the summary is a strengthening, and the C1
guard survives it.

Do not build the GC part as designed. Findings 7, 8 and 9 are concrete
defects: the arm record would carry no WireGuard site, the cancel model would
mismatch on every delete during a run, and the gap rule leaves the trace's
tail open while misreporting a guarded failure as a silent gap. Findings 10
to 12 and 19 are missing rules. Redesign it as its own stream (B4b), starting
with the suite-wide spike of findings 9 and 11 and with per-trace arming. Keep
the exclusion, with its reason sharpened, until that lands.
