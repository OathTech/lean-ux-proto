# Choice-stream strategy — 2026-10-03

Status: **direction agreed** [USER 2026-10-03: "Yes, this sounds like a good
direction"]. The details are proposed [AGENT] and were revised after a
critical audit (section 12). They go to the user's decisions in section 11,
after the measurement in section 10.

It supersedes the kernel mechanism of the
[steering design](2026-10-03-steering-design.md) (its sections 4.2 and 7.2).
Its semantics carry over: complete schedules, supplied values still recorded,
the exact schedule check, and expected outcomes.

## 1. Goals

The user's three criteria [USER 2026-10-03]:

1. **Natural inputs.** Run Linux on natural, or naturally generated, inputs
   and test correspondence.
2. **Light instrumentation.**
3. **Scale.** A strategy that plausibly scales to the kernel, at least in
   rough outline.

And the two questions it serves:
- **Correspondence:** given what Linux consumed, does the mirror do what
  Linux does?
- **Input selection:** randomized probing, where frozen vectors are fine.

## 2. Sources

A read-only survey of three local projects:
- **golean** (`/home/dev/projects/golean`): the machine draws from a supply
  stream. `Choices.consume` pops `c % bound` and yields 0 when exhausted, a
  fail-open default that project later measured and constrained
  (`GoLean/GoCore/State.lean:205-209`). The width rule is `consumeAt`: it
  pops only for sites with two or more options (`:443-446`). The sites form
  a datatype, and the Go side is sampled and checked for membership.
- **grossmith**: one chooser and a draw tape, with typed fail-closed replay
  errors (`gen/choice.go`), and shrinking by regeneration.
- **raft-proofs**: one jitter draw in the Go code is either recorded
  (`tools/differential/mirror_hooks.go:81`, `mirrorRecordDraw`) or forced
  from a labelled tape (`:59`, `mirrorTakeDraw`, still followed by a record).
  The Lean mirror consumes the same tape with the same checks. Concurrency is
  lifted into explicit driver actions.

Kernel facts are checked against `.deps/linux` and
`kernel/config-x86_64-net-hidden`, at the lines cited.

## 3. The model

These rules hold unchanged from the first version; the audit confirmed
them.

- **A program decision** is a C condition the mirror computes from mirrored
  state and the trace. It is recorded (`branch`, `branchCmp`) and checked
  against KCOV, never replayed. Replaying decisions would make the
  control-flow check vacuous.
- **A choice** is a value the C consumes that no mirrored state determines:
  - random draws;
  - clock reads;
  - allocation outcomes;
  - device and network bytes;
  - which deferred unit runs at a dispatch boundary.

  golean's width rule decides what is a choice: **a site is a choice only if
  the lab can give it more than one value.** So allocation outcomes are
  assumed today, with a single value.
- **Records are the only input the mirror consumes.** Each record carries:
  - a kind;
  - a call-site chain;
  - a value;
  - a steered flag;
  - a global sequence number.

  The mirror consumes records in sequence order. Mismatches, underflow and
  leftovers fail noisily.
- **Capture is the default; supply (steering) is for target states.**
  Supplied entries are still recorded. A schedule is a constraint checked
  against the records.
- **Replay** has two modes:
  - the mirror on frozen records, needing no kernel;
  - the kernel on a complete schedule, only as far as steered traces need.

## 4. The instrument

### 4.1 One primitive, one order

`kcov_choice(kind, data, len)` in `kernel/kcov.c`, an unanchored file. It:
1. runs the coverage context test (`check_kcov_mode`);
2. consults the trace's supply queue: a matching head is substituted, and a
   mismatch writes a marker;
3. writes the record.

**One order.** A global sequence counter (an atomic in `kcov.c`) stamps
every record (step 1). Section start and stop records follow with step 3. Task records
and remote sections then merge into one order. Today they merge by
convention (task before remote, `evaluator/check.py:202-204`), which fails
once task-context sites exist (`send.c:25-29` via `wg_xmit`). It also fails
because `kcov_move_area` copies a remote section at its *stop*
(`kcov.c:1041-1044`), so concatenation gives stop order, not start order.
The mirror treats sections as intervals: a section's records belong to that
section's deferred unit, at the position its start record gives.

### 4.2 Call-site identity

A record's site is identified by its **consumer frame**: the first frame of
its symbolized call chain outside the random and clock helpers (step 1 as
built). An inline helper used by several callers (`timers.h:28`,
`noise.h:103`) is one site for all of them. That is harmless, because records
are consumed in sequence order and A2 fixes which caller ran, and a surplus
record fails at the next read or at the operation's end. The full chain and
the tail-jump check remain for supply resolution in step 2. The innermost frame alone is not enough:
- both ephemerals are drawn through the inline `get_random_bytes_wait`
  (`include/linux/random.h:126`);
- several `noise.h:103` and `timers.h:26-29` callers share a line.

Two host-side checks:
- **No tail jumps.** No hooked function is reached by a tail jump `jmp`
  from a consumer (`evaluator/coverage.py:69-75` already finds such jumps in
  this build). A tail jump would hide the consumer's frame.
- **Supply resolution.** A schedule names a site by chain. The host resolves
  it to the return addresses whose chains match (under `nokaslr`) and loads
  them; the kernel compares addresses.

### 4.3 Generic capture points

| Kind | Where (6.12.110) | Notes |
|---|---|---|
| random | `get_random_bytes` (`random.c:428`); the batched `get_random_u8/16/32/64` (`:490-544`); `__get_random_u32_below` (`:546-579`) | `get_random_u32_below` with a non-constant ceiling is out of line (`random.h:60-62`): it records once, at `__get_random_u32_below`'s return, and its internal draws use an unrecorded `_raw` variant of the batched function. With a constant ceiling it is inline, and the batched draw records with the consumer's chain. Separate PRNGs do not bypass these (`prandom_u32` is gone in 6.12; the siphash keys are drawn before the window, `guest.c:152-170`). |
| clock | every exported reader in `kernel/time/timekeeping.c`: 17 wrapped readers (`ktime_get_snapshot`, PTP only, is not), including `ktime_get_coarse_real_ts64` (`fs/inode.c:2648`, pipes) and `ktime_get_ts64` (`fs/select.c:85`, epoll) | `jiffies` is a plain load and stays unhooked: in comparisons the comparison operands carry it (A3); where it reaches data it is a declared gap (section 7). |
| dispatch | `process_one_work` (`workqueue.c:3264`); `call_timer_fn` (`timer.c:1795`; **deferred**: the D1 kernel opens no timer sections, [AGENT] 2026-10-04); the `NET_RX` vector only, in `handle_softirqs` (`softirq.c:536`) | sections open only for dispatch functions in the **armed dispatch set** (section 4.4). `TIMER_SOFTIRQ` is excluded from the vector section, because a timer section inside a vector section would nest (`kcov.c:880`), and a nested stop closes the outer section. `RCU_SOFTIRQ` is excluded by construction, so RCU callbacks are unrecorded rather than debt. `KCOV_INSTRUMENT_softirq.o := n` (`kernel/Makefile:26`), so the dispatch code adds no PCs of its own. |

Each section writes a start record naming the dispatched function. For the
vector this is `net_rx_action`; the environment infers which skbs it handles
from backlog order. The stop record carries a count of records dropped in the
section.

**Silent section loss.** `kcov_remote_start` returns silently when the handle
is unregistered or the per-CPU area is unavailable (`kcov.c:884-918`). These
paths increment a dropped-section counter. The guest reads it after each
child and fails the trace if it is nonzero. A section whose block reaches
the area after its operation's readout is caught by the opened counter: the
check requires every opened section's start record in the trace (D1
integration, [AGENT] 2026-10-04, `evaluator/check.py` `section_problems`).

**Reschedules.** On this `CONFIG_PREEMPT_NONE` kernel a worker gives up the
CPU only at a `cond_resched` (or by sleeping, which the modeled workers do
not). `__cond_resched` writes a resched record (kind 302) when it is about
to schedule inside a task section, so a switch to a task without a section
is recorded too. The environment replays it (`Env.condResched`) (D1
integration, [AGENT] 2026-10-04).

### 4.4 The armed state, and the inter-trace boundary

Before each trace process, the guest's parent arms the trace state with one
ioctl on the remote KCOV fd:
- the common handle;
- the supply queue;
- the **armed dispatch set**: the dispatch functions the mirror models,
  resolved to addresses by the host. For WireGuard that is the handshake
  send and receive workers, the encrypt and tx workers, `net_rx_action`, and
  (deferred, not in the D1 kernel) WireGuard's timer callbacks.

Dispatches outside the set open no section and record nothing:
- vmstat, which runs every `HZ` (`mm/vmstat.c:2013`);
- RCU callbacks;
- netns cleanup.

That is the background-work policy for dispatched work: there is **no**
"environment noise" class for it, and so no fail-open loophole. (Section 10b
covers the one declared ambient clock consumer, the scheduler, which step 1
found inside the window.) A modeled worker of the trace runs
inside the set. Work outside the set is not the trace's. It is not checked,
and is stated as out of the mirror's scope.

**The inter-trace boundary.** At trace end, the guest deletes wg0
synchronously (`RTM_DELLINK`), before disarming. `wg_destruct` is the
device's `priv_destructor` (`device.c:376`) and runs in the deleting task:
it removes the peers, stops their timers and destroys the workqueues. No
earlier device's worker or retransmit timer (`timers.c:185`, 5 s plus
jitter) can then run under the next trace's state. Asynchronous netns
cleanup (`net/core/net_namespace.c:595,702`) remains, but `cleanup_net` is
not in the dispatch set. The deletion's own coverage lands after the last
operation and is discarded.

## 5. Cut consumers

Generic capture sees choices consumed below the mirror's cut. The first real
case shows that in-order, exact-count consumption is impossible. Every IPv4
datagram wg0 sends reaches `ip_idents_reserve` (`net/ipv4/route.c:469-484`).
That draws `get_random_u32_below(now - old)` **only if `jiffies` changed**
since the bucket's last use: 0 or 1 draws per packet, decided by a value the
mirror cannot see.

The rule, stated with its weakness:
- **Mirrored consumers are consumed exactly**, in sequence order, with site
  and value checks.
- **Cut consumers form a declared skip set per cut point.** A record whose
  chain matches a declared cut consumer of a cut point the operation passed
  through is skipped. It is counted and reported, but not count-checked.
- **Anything else is a `hidden_mismatch`.** That is a record from neither a
  mirrored consumer nor a declared cut consumer, or a cut consumer's record
  in an operation that did not pass its cut point.

This is weaker than the mirrored check, deliberately. The skip set is
bounded by being per cut point and attributed by chain. Each entry needs a
justification: why the value cannot reach mirrored state. An entry without
one is not added. The inventory of skipped records per run is part of the
report, so growth is visible.

## 6. Allocation outcomes (fault injection), revised

The first version's `fail_nth` plan does not work here:
- **GFP_KERNEL is never failed by default.** `failslab`'s
  `ignore_gfp_reclaim` is on by default and is checked before
  `should_fail_ex` (`mm/failslab.c:15,30`), so GFP_KERNEL allocations never
  fail.
- **No call-site identity.** `_RET_IP_` at `should_fail_ex` is
  `failslab.c:46` for every allocation.
- **Task context only.** `fail_nth` is honoured only in task context, so
  the send and receive workers' allocations are not reachable through it.

Revised plan:
- **Supply the outcome** through the kcov queue, at the slab and page fault
  hooks (`should_failslab`, `should_fail_alloc_page`, the usercopy hook).
- **Record the cache name and the allocation's caller chain.** That is two
  frames up, and reaching it needs the caller's IP passed explicitly or
  recovered from `slab_pre_alloc_hook`. This needs its own small design.
- **Prerequisites:** `CONFIG_FAULT_INJECTION`, `FAILSLAB`, `FAIL_PAGE_ALLOC`
  and `FAULT_INJECTION_USERCOPY`. The hooks do not depend on the debugfs
  knobs, and `verbose=0` silences the console dumps.

`envOk`'s sites stay assumed until this lands. It is roadmap step 5 and gets
its own design note.

## 7. Concurrency, and what is debt

**Capture.** On one CPU with `PREEMPT_NONE`, records merged by sequence
number give the execution order of armed sections. Within a task section,
interrupt-driven softirqs are sections nested in it, which is supported
(`kcov.c:876-879`). The mirror's environment becomes a record-driven
scheduler.

**Supply.** Schedules are not steered in the kernel. They are made
predictable by guest-side synchronization (waits inside the queuing
operations) and by steering values.

**Debt** (out of domain, stated):
- lockless interleavings (RCU, atomics, percpu counters);
- multiple CPUs;
- hardirq context, which includes hrtimers here (`CONFIG_HIGH_RES_TIMERS` is
  unset, and `check_kcov_mode` excludes hardirq, `kcov.c:179`), so
  hrtimer-driven behaviour is unrecordable;
- `jiffies` reaching data (the IP ident above);
- dispatches outside the armed set.

## 8. Input generation

Three layers draw from one generator tape, as in grossmith:
- the trace's operations (`evaluator/generate.py`);
- steering schedules for target states;
- environment knobs (waits).

Shrinking regenerates and re-runs the kernel per candidate, with the domain
filter pruning first. A live coordinator stays deferred: steering removes
the need for D1.

## 9. Change footprint, honestly

**The generic design** touches six to seven core files:
- `kcov.c` and `kcov.h`;
- `random.c`: six functions;
- `timekeeping.c`: 18 readers, by one uniform macro;
- `workqueue.c`, `timer.c` and `softirq.c`: one site each;
- later, the fault hooks.

**The per-site design** touches eight files today, all WireGuard-local.

So the claim is **fewer hooks per subsystem, not fewer hooks**. The
scalability test (section 10, step 7) is that the next subsystem needs zero
new hooks: only declarations (mirror sites, cut consumers, dispatch-set
entries).

## 10. Roadmap, each step with its evidence

0. **Measure first: the enumeration probe** (the "audit variant" the
   hidden-inputs design planned and never ran). A throwaway kernel in a
   worktree records every generic random and clock call in the window, with
   its chain. It runs the WireGuard and generated suites, and reports per
   operation: the consumers, their counts, and which are mirrored, cut or
   unknown. It also measures the sequence-merged section order against
   today's convention. This replaces section 5's guessed inventory with
   counts, before any oracle change.
1. **Generic capture of random and clock reads, with the sequence number,
   the chain identity and the cut skip sets.** Retires the four WireGuard
   hooks.
   - **Evidence:** the clock-driven decisions (the flood test,
     `noise.c:636-638`; the rate limit, `send.c:25`) become `branchCmp`s
     with recorded operands. A **threshold** mutant (50 → 5 initiations
     per second) survives today, because every in-domain gap is at least
     400 ms, so the outcome never changes. After this step A3 rejects it,
     because the compared operand `last + NSEC_PER_SEC/IPS` differs. The
     inverted-comparison mutant is already rejected today by A1, so it is
     not claimed.
   - **Negative controls:** H-M6, an undeclared consumer, and a cut
     record in an operation without its cut point.
2. **Supply on the same primitive.** Steering schedules, the exact check
   and expected outcomes. Also a trace class with steered clocks closer
   than 20 ms, which reaches the flood arm.
3. **Armed dispatch sections with worker records.** Retires the per-site
   sections; adds synchronous wg0 deletion.
   - **Evidence:** a mirror mutant that swaps two deferred units is
     rejected; the dropped-section counter stays at zero.
4. **The WireGuard initiator role (D1)**, as scoped in the steering
   design.
5. **Allocation outcomes** (section 6, its own design note).
6. **Tape-based generation with shrinking.**
7. **The scalability test.** The next subsystem (pipes or epoll) needs only
   declarations.

## 10c. Step 1 results [AGENT 2026-10-03]

The user approved step 1. It is built on this branch; the oracle change needs
the user's approval.

**Kernel `net-choice`:** the B2 remote-coverage patch plus
`kernel/patches/choice-stream.patch` (sha256 `b662b463…`), with identity
`d8884037…` in `kernel/identity-x86_64-net-choice.txt`.
- `kcov_choice_ip` records each choice: kind, call site, sequence number,
  length, value.
- The hooks are the five random entry points (`__get_random_u32_below`
  records once, through a `_raw` split) and 17 wrapped clock readers.
- WireGuard's four per-site hooks are retired. The send worker's section
  stays until step 3.
- The config is identical to the current oracle's apart from the version
  string.

**Mirror:**
- **14 WireGuard sites.** The four already recorded; nine clock reads that
  were assumptions before (`last_sent_handshake` at `noise.h:103` and
  `send.c:29/39/89/102`; `wg_birthdate_has_expired` at `timers.h:28`; the
  flood test and consumption time, `noise.c:637/650`; the keypair birthdate,
  `noise.c:396`); and the retransmit jitter (`timers.c:186`) with the C's
  exact rejection loop.
- **Replaced:** the `lastSentExpired` flag and `Timing.sinceLastConsumption`,
  by recorded values.
- **Clamping:** the ephemeral secret is clamped by the mirror, from the raw
  draw.
- **Cut and ambient:** four cut sites are consumed at their cut points (the
  fixture's own send, `wg_xmit`'s ICMP error path, wg0's send cut). One
  ambient site, the scheduler (section 10b).
- **The flood test** is a `branchCmp` on the recorded clock. Its compare is
  assigned to `flood_attack` at `noise.c:635`, so the decision table gains an
  explicit, bounded `assigned` comparison: it must precede the condition
  within six lines. Only this decision uses it.

**Evaluator:**
- records are mapped to sites by consumer frame;
- they are ordered by sequence number across the task and remote streams;
- an undeclared consumer or an unknown kind is a problem;
- skipped records are reported (`choice_records_skipped`).

**Generator:** planned guest waits now stay within 2.8 s of the 4 s bound.
One borderline trace had tipped over.

**Full check** on `e8fd900` (clean tree, `vmlinux` `ef103305…`):

| Check | Result |
|---|---|
| Behavior | 1,325 / 1,325 traces agree (38,934 operations) |
| Control flow | all agree |
| Operands | 320,655 pairs (the flood test's comparisons are new) |
| Choice records skipped (coverage child) | `ip_idents_reserve` 345, `ip_ident_key` 127, ICMP 106, flow-hash secret 7, scheduler (ambient) 11 |

**Mutants:** 27 of 30 rejected.
- **H-M7, the flood threshold (5 instead of 50 per second):** rejected only
  by A3, "operands differ from Linux", on 9 traces. Its outcome never flips
  in the domain, so this is the evidence step 1 pays for itself: the mutant
  survives without recorded clocks.
- **H-M9** (`last_sent_handshake` not set back) and **H-M11** (cut records
  without their cut point): rejected by `hidden_mismatch`.
- **H-M10** (an undeclared cut consumer): rejected by "choice from an
  undeclared consumer".
- **Survivors:**
  - **B2-M3 and C-M3**, as documented before.
  - **H-M8**, the unclamped response ephemeral. This is an equivalent
    mutant. The kernel's `curve25519` clamps its scalar internally
    (`lib/crypto/curve25519-hacl64.c:772`), as does the mirror's RFC 7748
    `x25519`. So `curve25519_generate_secret`'s clamp changes no output;
    only the unobserved stored secret differs.

**Review.** An independent Fable review found one wrong behavior: choice
records were split only in network traces, so FS paths' clock reads would
have corrupted coverage. Fixed: every trace. The FS suites pass, and today's
FS slice makes no in-window clock reads. Also fixed:
- double recording in two fast readers;
- a dead cut entry;
- unknown kinds were mapped as clock reads;
- skipped records were not reported;
- a missing negative control (H-M11);
- the jitter ceiling from `HZ`;
- the documentation (sections 4.1–4.3, 10b).

## 10d. Step 2 results: steering [AGENT 2026-10-04]

The user approved continuing to step 2 ("Great, continue").

**Kernel:** `choice-stream.patch` (sha256 `9b75e58e…`, identity `d0123d1b…`).
- **The schedule** lives on the trace's remote KCOV instance and is loaded by
  ioctl (`KCOV_LEANUX_STEER_LOAD`) in the guest's parent before it forks the
  trace process.
- **Finding it:** from a remote section through `t->kcov`; from the trace
  process's own context through `kcov_remote_find` on its inherited handle.
- **Matching:** at a call site the schedule names, the encounter must match
  the head entry, by kind and return address. A value entry is substituted
  into the caller's buffer, and its record carries the steered bit (`0x8000`).
  A "draw" entry keeps the kernel's value.
- **Failures:** a non-match writes a `0xffff` marker record. The parent reads
  back what is left and the mismatch count (`KCOV_LEANUX_STEER_STATUS`).
- **Scope:** sites the schedule does not name are untouched. Only recording
  contexts steer.

**Harness and check:**
- **Resolution:** `harness/steer.py` resolves each site label to the return
  addresses of the hooked calls whose consumer frame is that site. It
  disassembles `vmlinux`, and the result is cached per kernel. It refuses a
  site in a function that tail-jumps to a hook, and checks each site's domain
  (only the four steerable sites; the `tai64n_now` bounds).
- **Exact check, per child:** the records at the named sites must be the
  schedule, entry for entry: the label, the steered flag and the value.
  Markers, leftovers and status rows are problems.
- **Expected outcomes:** a steered trace's `expect` labels must be reported
  in the mirror's run. That run agrees with Linux on behavior and control
  flow, so this is a mirror-reachability check gated by A1 and A2, not a
  direct assertion on Linux's coverage. Of the two corpus outcomes,
  `wg_index_hashtable_insert.unlocked_collision=1` and
  `wg_index_hashtable_lookup.type_matches=0` have no KCOV witness in this
  build. The collision is still confirmed on the Linux side by the three
  steered index records, a count only the C's `goto search_unused_slot`
  produces, checked exactly.
- **Domain mode:** placeholders follow the schedule per site (not across
  sites) and reject a value of the wrong length. They are looser than the
  authoritative check, which is the one that decides.

**Results:**

| Measure | Result |
|---|---|
| Full check on `90f90c7` (clean tree, `vmlinux` `04f2959f…`) | 1,327 / 1,327 traces agree (38,943 operations), 320,693 operand pairs |
| Steered traces | `s2_index_collision` (an unlocked collision, then a redraw) and `s2_lookup_hits_handshake` (a data message naming a live handshake index); both schedules fully consumed with no mismatch in both children |
| Controls (`scripts/steering-controls.py`) | an unreached site, an extra entry and out-of-order entries each fail with their problem |
| Mutants | 30 of 32 rejected. S2-M1 (the lookup ignores its type mask) and S2-M2 (no redraw after a collision) are reachable only through the steered traces, and are rejected. Survivors: B2-M3, C-M3 and H-M8 (equivalent), as before. |

**Caveats, stated:**
- **The schedule's lifetime is safe by the guest's discipline.** The parent
  loads before forking and reads back only after `waitpid`, and nothing
  reloads or disables in between. The kernel takes no reference across the
  lookup.
- **The kernel trusts the host for value domains.** For example, a steered
  `__get_random_u32_below` value is substituted after the C's bounding. The
  harness is the only producer of schedules, and it checks.
- **Tail jumps.** `wg_timers_handshake_complete`'s wall-clock read
  (`timers.c:197`) is reached by a tail jump. Its records are attributed to
  the caller's caller, and the site cannot be steered. D1, which needs that
  record, must declare it accordingly.

**Review.** An independent Fable review found no wrong or fail-open
behavior. It found three claims the code did not back (now fixed or
reworded): the tail-jump guard (implemented), the `expect` semantics (stated
above), and stale design text (the steering design's status). It also found
nits: duplicated helper lists (now one), the domain-mode value length (now
checked), the control suite's error text, and the caveats above.

## 10b. Ambient sites (step 1)

Step 1 adds one class the earlier text ruled out. Scheduler bookkeeping
(`start_dl_timer`, `kernel/sched/deadline.c:1153`, reading `ktime_get`
through `hrtimer_cb_get_time`) reads the clock wherever the task sleeps or
wakes. It belongs to no cut point the mirror models.

It is declared as an **ambient** site, consumed wherever it occurs. The
class is bounded:
- it is one declared consumer frame;
- its records are counted per run (`choice_records_skipped`);
- any other undeclared consumer still fails.

This is weaker than the cut rule (no position at all), and is accepted
because the mirror does not model the scheduler (one CPU, `PREEMPT_NONE`).
Adding a second ambient site needs the same justification as a cut entry.

## 10a. Step 0 results [AGENT 2026-10-03]

The user approved step 0. The setup:
- **Kernel:** a throwaway `net-probe` kernel in this worktree. It is built
  from the merged oracle patches plus
  `kernel/patches/probe-choice-enumeration.patch`, which adds generic hooks
  at `get_random_bytes`, the four batched `get_random_uN`,
  `__get_random_u32_below` and the 17 exported clock readers, plus section
  start and stop records, each with a global sequence number.
- **Guest:** splits these records out before anything else reads the area.
- **Analysis:** `scripts/probe-choice-enumeration.py`.
- **Runs:** the WireGuard suite and the generated WireGuard suite, 252
  traces in all.

| Measure | Result |
|---|---|
| The check on the probe kernel | 52 / 52 and 200 / 200 agree, operand pairs unchanged (1,289 and 7,417): the probe perturbs nothing observable |
| Per-site records with a generic record at the same chain and value | **176 / 176** (ephemerals after clamping, the index draw, the timestamp) |
| Remote sections; nested or overlapping; start order ≠ stream order | 483; **0**; **0** |
| Operations where a task-context record follows a remote section's start | **0** in these suites |

**Inventory: 20 distinct consumer sites** across all 252 traces, with record
counts:
- **WireGuard, already recorded (4):** `noise.c:541` (30), `noise.c:688`
  (45), `noise.c:501` (28), `peerlookup.c:132` (73).
- **WireGuard clock reads behind the `Timing` contract and the
  `lastSentExpired` flag (9):**
  - `noise.h:103` `wg_noise_reset_last_sent_handshake` (647)
  - `timers.h:28` `wg_birthdate_has_expired` (146)
  - `send.c:29` (58), `send.c:39` (28), `send.c:89` (45), `send.c:102` (45)
  - `noise.c:637` (52) and `noise.c:650` (45), the flood bookkeeping
  - `noise.c:396`, `derive_keys` (45)
- **WireGuard random, unrecorded (1):** `timers.c:186`, the retransmit
  jitter (29).
- **Below the cut (5):**
  - `ip_idents_reserve`, `route.c:482` (361, each with an inner
    `get_random_u32` record, which needs suppression as planned);
  - `__ip_select_ident`, `route.c:497`, the per-netns ident key (130);
  - `icmp_global_consume`, `icmp.c:268` (96, from ICMP port-unreachable on
    closed loopback ports);
  - `__flow_hash_secret_init`, `flow_dissector.c:1710` (5);
  - `ktime_get` via `hrtimer_cb_get_time` (7).
- **Unknown: none.**

**What it settles:**
- **The generic design finds every site the per-site hooks do**, at the
  same chain and value, with no new hooks.
- **The cut skip set has five entries,** each with a clear reason its value
  cannot reach mirrored state.
- **Ordering assumptions hold in today's suites**, so the sequence number
  is insurance for D1's interleavings rather than a correction to current
  results.
- **The ten WireGuard clock and jitter sites are step 1's real payload.**
  Each turns an assumed contract into a recorded, checkable value.

## 11. Decisions for the user

1. **The model** (section 3), which the audit found sound.
2. **The revised mechanism:** the sequence order, chain identity, the armed
   dispatch set, synchronous teardown, cut skip sets with their stated
   weakness, and no environment-noise class.
3. **Step 0, the measurement probe,** as the next action. It needs no
   oracle change.
4. **Later steps' kernel or config changes,** each returning for approval
   as an oracle change.

## 12. Audit [AGENT 2026-10-03]

An independent Fable audit found three blocking defects in the first
version:
- **Nested dispatch sections.** Timer sections sit inside the timer softirq
  vector; a nested start warns and the inner stop closes the outer. And
  every vector was sectioned, including RCU. Now the dispatch set is armed
  and explicit (sections 4.3–4.4).
- **Exact consumption of cut records is impossible** because of
  `ip_idents_reserve`'s `jiffies`-dependent draw. Now there are skip sets,
  with their weakness stated (section 5).
- **A lab-wide handle plus asynchronous netns teardown** would put the
  previous trace's device workers in the next trace's window. Now teardown
  is synchronous and dispatch is armed (section 4.4).

It also found serious issues:
- the stream had no order across task and remote records (now a sequence
  number);
- call-site identity broke under inlining and tail jumps (now the full chain
  and a `jmp` check);
- the fault-injection plan was wrong (now supply through the queue, as its
  own design);
- the step-1 evidence was false (now restated as A3 on a threshold mutant);
- the background policy was miscalibrated and fail-open (now the armed set;
  noise class dropped);
- only four of 18 clock readers were listed;
- section loss was silent.

And minor ones: the golean description; a vector's section name; supply
resolution under inlining; the footprint claim; measuring before deciding.

**One audit claim was wrong.** It could not find raft-proofs' capture and
force code; it exists at `tools/differential/mirror_hooks.go:59,81`.
