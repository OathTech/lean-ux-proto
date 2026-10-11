# Decisions register

Standing decisions, in date order, each with its provenance: `[USER]` for a
decision the user made, `[AGENT]` for one an agent made under delegated
scope. Design-level decisions also live in the design doc they belong to;
merge approvals also live in the integration record under
`.artifacts/runs/evidence/<id>/integration.json`. The rules that follow from
these decisions are in [AGENTS.md](../AGENTS.md), without this history.

## 2026-09

- **2026-09-22 [USER]** Direction: the deliverable is a purely operational,
  executable Lean mirror of the configured Linux code at the thin-layer
  altitude, tested against kernel behavior; no theorem proving of any kind.
  Worktrees and explicit user signoff for every update of `main` are a core
  trustworthiness requirement for every agent, including the coordinator.
  The rule is prospective; no remediation of earlier commits was requested.
- **2026-09-29 [USER]** Direction restated. The
  [way-forward plan](2026-09-29-way-forward.md) adopted; its questions D1 to
  D7 are answered in its section 7. The mirror abstracts C semantic detail
  but keeps a simple correspondence of data structures and control-flow
  choice points, so that a separation-logic triple can later host the
  Linux-to-mirror relation (the anticipated tool is the user's cerberus-sl
  prototype; that project is read-only from here).
- **2026-09-30 [USER]** Checks must pay for themselves, after the drift
  audit: "We know roughly what we need, ie. data and control equivalence over
  the executable mirror. If we have that, we're building a reasonable digital
  twin. I'm happy to put the monitor infra 'on a diet' but we don't need to
  get sent on a sidequest."

## 2026-10

- **2026-10-01 [USER]** Refinement: "I think we can add further checkers, we
  just need to make sure they 'pay the bills'. I.e we don't add checkers that
  just accrete. But finer grained instruments are okay."
- **2026-10-03 [USER]** Hidden inputs are recorded at their source. Linux
  paths that depend on hidden values (randomness, clocks, external inputs;
  later, scheduling) have those values captured by kernel probes with
  call-site identity; the mirror is a deterministic function of the trace
  plus the records, fail-noisy on mismatch. Seeding the RNG and inferring
  from outputs were rejected as primary mechanisms. Agreed "entirely".
  ([hidden-inputs design](2026-10-03-hidden-inputs-design.md))
- **2026-10-03 [USER]** The choice-stream strategy ("Yes, this sounds like a
  good direction"): one labelled choice stream captured at generic kernel
  interception points; steer only what a target needs, and record supplied
  values too; the mirror consumes records only; the scale test is a second
  subsystem that needs zero new kernel hooks.
  ([choice-stream strategy](2026-10-03-choice-stream-strategy.md))
- **2026-10-04 [USER]** The dispatch-section opened-count check
  (`evaluator/check.py`, `section_problems`) stays although no mutant is
  rejected by it alone: it closes a silent-pass hole, is cheap, and has had
  no false failures. This resolves, for this check only, the conflict between
  "checks must pay for themselves" and the global rule that fail-open
  behavior is a defect. It is not a licence to add checks that accrete.
- **2026-10-04 [USER]** Depth sequence after D1: D2 (WireGuard data plane),
  then D3 (timers, with the timer-firing instrument), then pipes as the scale
  test; allocation outcomes and DoS/cookies/ratelimiter after. The goal is
  "complete on one CPU"; SMP and lock-free interleavings are research debt,
  not a stage.
- **2026-10-05 [USER]** Orchestration: parallel workstreams (D3 timers, E
  DoS, L lifecycle, A allocation, P pipes) toward complete single-CPU
  WireGuard coverage, pipes as an additional test; serial single-agent runs
  are not wanted once the instruments exist. `LEANUX_QEMU_SLOTS` is 3. The
  D3 design, its clocksource (`refined-jiffies`) and its scope approved.
- **2026-10-06 [USER]** The host is contended: "I'm running a lot of jobs on
  this box. I'm working on getting another box running, but in the mean
  time, assume the box is somewhat contended." Check failures under load are
  modeling gaps, not flakes: fix them in the environment model with exact,
  fail-closed rules, never with retries
  ([contended-host note](2026-10-06-contended-host.md)).
- **2026-10-06 [USER]** Coverage goal: "we should try to get to 100% coverage
  of 'reasonable' single-CPU wireguard. I.e if there's some profound reason
  it's hard, no harm. But for things that seem in reach and can reasonably be
  differentially tested, let's get there." Exclusions record their reason.
- **2026-10-06 [USER]** A2 (task-context forced allocation failures) is in
  scope as a declared failslab-style extension. The A, E and L design
  decisions are recorded in their design docs (commits `58f7afd`, `3da3431`,
  `11acb1a`).
- **2026-10-07 [USER]** The WireGuard boundary: "we should stop at the
  boundary of wireguard (unless this breaks important things)." The IP stack
  is modeled only where WireGuard's code paths or observables depend on it;
  the ICMPv4 ident capture (K6) is deferred; stack behavior is pinned with
  fixture sysctls where that is cheaper than modeling it. T1 (per-NET_RX-
  section placement agreement for bulk traces) and U3 (the future-proof-paths
  conventions in [the note](2026-10-06-future-proof-paths.md), with a pointer
  in `AGENTS.md`) approved. W4+W7 decision 13.2 (ii) and W5+W6 decision D2
  approved.
- **2026-10-07 [USER]** Oracle kernel changes: record-only or steer-only
  changes (new choice records, capture hooks, steering lookups, the dispatch
  cap size) are approved as a class, each still landing with per-merge
  signoff and its identity and patch hash recorded; changes that alter kernel
  behavior or configuration (`CONFIG_PACKET`, boot parameters, functional
  patches) each need their own case. The batch covered: the queue-depth
  capture, the route-cache jiffies records (kind 306), `KCOV_DISPATCH_MAX`
  16 to 32, A2's own-fd steering fix.
- **2026-10-07 [USER]** D3 merged to `main` (`84a56fd`): "yes approved on
  both", covering the merge, kernel identity `8744fcc4...` and the boot
  parameter `clocksource=refined-jiffies`.
- **2026-10-08 [USER]** No validation grind: "The subagent has run for 2
  days. This surely isn't worth the grind?" The L follow-up agent was
  stopped. Agents are time-boxed with a stop condition; mutant runs are
  scoped to the touched mirror files on a reduced corpus, the full set once at
  a milestone; no unrequested harness or guest changes during validation.
- **2026-10-08 [USER]** The project pauses for the move to a new machine
  ([pause-state note](2026-10-08-pause-state.md),
  [setup guide](SETUP-new-machine.md)).
- **2026-10-08 [AGENT, coordinator]** Scope rulings under the boundary
  decision: MTU 0 and poll-budget exhaustion in scope; `ip_error`, suspend
  and the ICMPv4 identifier capture deferred; link flags in W8b dropped;
  tstats provisional; W13 (second device) last; the three approved sysctls
  held back because nothing kept by the boundary rule needs them.
- **2026-10-10 [USER]** Global policy (`~/.claude/CLAUDE.md`): auto-memory is
  off; `AGENTS.md` is a working-practices doc, not a log; decisions are
  logged with provenance in commit messages or the project's decisions file,
  never in `AGENTS.md`; every heavy job runs through the box-wide `capped`
  wrapper, and any local capping script is replaced by it; worktrees, `.tmp`
  and stale `.lake` directories are removed when done.
- **2026-10-11 [USER]** The kernel identity is validated: "agree re adding
  validation asap (once the run is over)". Every check and every guest boot
  compare the selected build with the approved identity and refuse any other
  build; the evidence is the D3 S2 incident and the 2026-10-11 baseline that
  nearly ran on the pre-D3 build left in the default directory.
- **2026-10-11 [USER]** Dispatch order is recorded at the source (option A):
  "Okay, let's do (A)". The order in which Linux dispatches queued deferred
  units is a hidden input: `__queue_work` records the work item it queues,
  the arm record names its timer, and a dispatch section names the unit it
  runs, so the mirror follows the records instead of assuming queue order.
  Record-only kernel change, in the approved class; the merge's signoff
  covers the new identity. Found by `s2_index_collision`, which failed in
  about two of three fresh-guest runs while passing in every chunked full
  check ([the design](2026-10-11-dispatch-order.md)).
- **2026-10-11 [AGENT]** This register created from the retired agent memory
  and the dated history formerly in `AGENTS.md`; the 2026-10-07 orchestration
  snapshot is superseded by the pause-state note. The checker's model build
  and `scripts/build-kernel`'s `make` call `capped` themselves, fail-closed
  when the wrapper is absent (`LEANUX_CAPPED` overrides its path). Pending
  the user's signoff.
