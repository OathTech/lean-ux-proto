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
  [setup guide](history/SETUP-new-machine.md)).
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
- **2026-10-12 [AGENT, coordinator]** W9's fixture order: after a successful
  flag-changing `wg_up` the guest waits (its existing post-up wait, moved)
  before adding wg0's addresses and routes, and the mirror applies those
  table changes after the operation's send workers and idle timers. The
  handshake worker queued inside the ioctl ran before the route adds in one
  run and after them in eight others; each add flushes `rt_genid`, which
  decides whether the dst that send cached survives, and nothing records
  the order. A fixture choice, not a placement the check reruns
  (docs/2026-10-06-w8-w9-netns-routing.md, section 14.3b).
- **2026-10-12 [USER]** Gates and speedbumps, applying the global guidance to
  this project: "I'm happy for you to recommend any level of gate
  preservation so long as each gate pays its way. Strong gates protect trust
  surfaces. Speedbumps prevent mistakes. Evertyhign else gets cut" [sic].
  Earlier the same day: "I am highly skeptical of 'certificates' / run
  recordings, etc for anything which is not a hard trust surface. Gates need
  to pay their way in trust."
- **2026-10-12 [AGENT, coordinator]** The cut list under that ruling. The
  gates are the model build with the unit tests, the differential check on
  the approved oracle at a claim point with its fail-closed instrument
  guards, and the kernel identity check. The speedbumps are the negative
  control suites and a sentinel mutant set, about ten WireGuard and two
  pipes entries, one per verdict channel and record instrument, on reduced
  corpora, at integration claim points only. Cut: the mutant catalogue
  beyond the sentinels (history keeps it), the "mutant it alone rejects" bar
  for a new check rule (now: cheap, and it catches a real class of mistake;
  a one-off mutant only for a new instrument on the trust surface, run once
  and reported in its commit), the integration records and evidence
  directories (the signoff and the run's counts go in the merge commit
  message), the per-chunk provenance hashing of inputs and tool versions
  (the kernel identity and the commands stay), the decision-coverage table
  in every report (an on-demand census), run-by-run validation narratives
  in design docs (a short table per stream from now on), and the
  environment acceptance scripts nothing uses.
- **2026-10-11 [AGENT]** This register created from the retired agent memory
  and the dated history formerly in `AGENTS.md`; the 2026-10-07 orchestration
  snapshot is superseded by the pause-state note. The checker's model build
  and `scripts/build-kernel`'s `make` call `capped` themselves, fail-closed
  when the wrapper is absent (`LEANUX_CAPPED` overrides its path). Pending
  the user's signoff.
- **2026-10-12 [AGENT]** The coordinator's decision on the W batch's claim
  point: the mirror follows W2's guest step now rather than waiting for the
  user's W2 rulings (question 2, the 3776-byte receive, was recommended yes
  and its guest half is on the branch). Hidden alloc site 21 (`netlinkDump`)
  moves from `af_netlink.c:2284` to `:2290`, the allocation the kernel takes
  when every receive is 3776 bytes; :2284 is dropped, not kept as a second
  site, since no modeled path receives more than 3776 bytes on a netlink
  socket. The last device's delete gains the below-cut alloc site
  `dAllocSlabDebugfs` (`fs/namei.c:1730`, the slab cache's debugfs dentry at
  `kmem_cache_destroy`), consumed at `ratelimiterUninit`, permissive: a
  chunk records it only when its steered sites arm the dentry cache's
  range, so its absence cannot be told from the records. The same armed
  lifecycle chunks showed `nlmsg_new` records between `wg_create`'s two
  neighbour draws and before an up device's `wg_destruct`; both are cut
  points now (`docs/2026-10-05-l-lifecycle.md` 16.3).
- **2026-10-12 [USER]** `capped` is an on-box matter: "My sense is that
  capped is an on-box matter, and that for everyday people, they shouldn't
  need to worry about it." The checker and the kernel build use the wrapper
  when it is installed and run uncapped with a notice otherwise; the box rule
  for agents is unchanged.
- **2026-10-12 [USER]** The next targets are epoll and seccomp, as parallel
  streams ("okay, I buy it. Let's do epoll and seccomp next, as parallel
  efforts"), chosen from the kernel scout's ranking: epoll as the readiness
  foundation (the wait-queue and poll contract), seccomp as the security
  target with its own theorems (chain monotonicity, checker soundness,
  translation correctness). seccomp's `SECCOMP`/`SECCOMP_FILTER` are an
  additive configuration change under the 2026-10-07 rule: the case is open
  by this decision, the identity comes with the merge. The eBPF engine below
  `seccomp_run_filters` (kernel/bpf/core.c) is a service with a stated ISA
  contract, never anchored: the user's separate eBPF JIT project owns that
  seam. The KVM config case (KVM, KVM_AMD, HIGH_RES_TIMERS: a
  behaviour-and-config change needing the D3 timer re-validation) stays open.
- **2026-10-12 [AGENT, coordinator]** Shared-table allocations for the two
  streams, append-only per the interface note: wire opcodes 27-29 epoll
  (`epoll_create1`, `epoll_ctl`, `epoll_wait`), 30-34 seccomp (install, the
  filtered probe call, `prctl` no-new-privs, two spare); record kind 308
  epoll's tree-insert file address (record-only, class-approved); HiddenSite
  ids 190-199 epoll, 200-219 seccomp (moved to 400-419 by the interface
  commit of 2026-10-12, since 200-219 is a worker section range); both
  streams' kernel changes go into one oracle rebuild after both designs are
  audited (in the event two: e2 for epoll, s1 for both with the seccomp
  config).
- **2026-10-13 [USER]** The seccomp config case and the P9 widening, put as
  one case (`docs/2026-10-12-seccomp-design.md` section 16): "Agree, sounds
  good - approved". So the oracle gains `CONFIG_SECCOMP=y` (and with it
  `CONFIG_SECCOMP_FILTER=y`, nothing else), a configuration change under the
  2026-10-07 rule, re-validated by the full differential check on the new
  oracle at seccomp's claim point; and the P design's user decision P9
  (`kernel/signal.c` mirrored down to the pending set) widens to the
  generation of an unblocked `SIGSYS`: `force_sig_info_to_task`,
  `complete_signal`'s wake arm for one task, its sigqueue allocation and the
  pending flag; delivery stays an environment effect; stop and continue
  signals, group delivery, real-time signals and a second thread stay
  unsupported. Recorded by stream X at phase 2a.
- **2026-10-12 [USER]** The seccomp prefill fixture, queued: "Yes, let's
  queue it". A `seccomp_prefill: N` top-level fixture key: the guest installs
  N copies of a fixed 4096-instruction filter before the window, under the
  no-new-privs step, shaped so the cache marks every probed number
  constant-allow; the mirror's initial task state carries the chain,
  reconstructed by its own translation of the same program (an `Env.lean`
  fixture assumption). It makes `seccomp_attach_filter`'s path budget
  (`MAX_INSNS_PER_PATH`, `-ENOMEM`) reachable within the guest's console
  limit, which 42 recorded installs of 768 instructions are not
  (section 7). Recorded by stream X at phase 2a.
- **2026-10-12 [AGENT, fork of the coordinator]** The epoll design
  (`docs/2026-10-12-epoll-design.md`) is drafted for the user's reading, no
  code. Its four decisions for the user (section 13): tier 1 is timeout 0
  with blocking waits `unsupported` until a scheduler record exists; a
  record-only kind-308 hook at `ep_rbtree_insert` carrying the file address
  (a new oracle, class-approved under "Oracle kernel changes"); the rbtree
  as an ordered-map cut with `ep_find` and `ep_rbtree_insert` declared cut
  functions rather than a Lean red-black tree; nested epoll in tier 1.
  Tactical choices made under the standing delegation: the wire mapping
  and the opcode proposal 27-29 (the coordinator allocates), the
  `max_user_watches` fixture check (fail-closed, like the identity), one
  wake-order sentinel plus a one-off record mutant. The scout's profile is
  corrected on one point: the `ovflist` has no producer in a single-task
  domain, so it is modelled but unexercised.
- **2026-10-12 [AGENT, coordinator]** The epoll design's tactical choices
  are decided as recommended, not put to the user: tier 1 is timeout 0;
  the rbtree is an ordered-map cut by listing `ep_find` and
  `ep_rbtree_insert` as decision-free functions, no new checker rule;
  nested epoll is in tier 1 with both arms of the reverse-path limits; the
  guest's fixture warms `loop_check_gen` up at boot and the mirror's
  counter is relative, its three comparisons' operands excluded; the
  `max_user_watches` fixture check is required; the only new mutant is the
  kind-308 one-off. The one decision that is the user's is the record-only
  kind-308 hook, presented at the claim point's merge signoff with the new
  identity. The design is revised to v2 (section 14, the audit response to
  section 15) by the fork, every corrected line re-read in 6.12.110.
- **2026-10-12 [AGENT, stream S]** The epoll mirror's wake callback and
  `ep_poll_safewake` live in `Leanux/FS/Wait.lean` in one mutual group with
  the wait-queue walk, fuel-bounded by the nesting the loop check admits;
  `ep_ptable_queue_proc` in `Poll.lean`; `__fput`/`__fput_sync` and the
  release dispatcher in a new `Leanux/FS/Fput.lean` after the epoll mirror:
  the module order follows the C's call graph (design 4.2, 4.6). The
  mirror's line numbers are the pristine source's, which the check reads;
  the kind-308 hook must keep fs/eventpoll.c's line count before the claim
  point (design 16.1), a kernel-patch change put to the coordinator, not
  made here.
- **2026-10-12 [AGENT, stream S]** The epoll settling pass changes two
  evaluator rules, both for facts of the built code and the guest: a
  shared exit may name a frame chain that several instrumentation points
  share (`points` in `correspondence/kcov.json`, the compiler giving a
  helper's test and its join the same frames), and an operand exclusion
  needs a comparison row at a declared call site rather than one row per
  report, since the guest deduplicates identical rows. The mirror's control
  flow did not change in the pass (design 16.1).
- **2026-10-12 [AGENT]** The simulation-target review's change 1 is
  implemented: dispatch identities are lifetime-scoped (retired at the
  peer's release and at `free_netdev`), and the last device's
  `wg_ratelimiter_uninit` uninitializes populated tables as the C does; the
  review's recommendation, not a change to any standing rule.
- **2026-10-12 [AGENT, coordinator]** W7 phase 2 decided yes on the phase-1
  count (design 17.11), under the user's delegation of tactical decisions;
  then stopped at the course check against the simulation-target review
  (3.5, 4.1, 4.2): the nested-resume form was removed before any commit, the
  step split of the draining workers kept, and phase 2 is to be built on
  suspended activations over a packet store with identities and a ring with
  cursors (design 17.15).
- **2026-10-12 [AGENT, coordinator]** Review change 2 implemented as an exact
  effect contract for the flood's invalid tail (`floodTailEffect`), not as a
  model of the tail's packets: their bytes are not in the trace, their state
  effects are entirely in their records. The C's `handshake_queue_len` counter
  joins the device state; the decay is computed from the recorded clock and
  resets the static (decision `decay_expired`). `World.floodDepth` is gone.
  The first checked cookie reply (`e_underload_live`) showed receive.c's two
  cookie arms cross-jumped into one block at :162; the spans now attribute it
  to `needs_cookie_mac` and leave the switch's initiation arm unobservable,
  rather than extending the checker (docs/2026-10-05-e-dos.md, appendix).

- **2026-10-12 [AGENT, coordinator]** W2's rulings on section 8 of the
  netlink design (`docs/2026-10-06-w1-w2-netlink.md`), made by the
  coordinator under the user's direction of the same day ("you are
  empowered to make tactical decisions" towards a control-and-data mirror).
  Yes to 1 (descriptor 8 as the stepped dump's fixture socket, the two
  fixture shapes, L's temporary socket at 9, `rlimit_nofile` at least 9 and
  10 with a lifecycle operation), 2 (the 3776-byte receive with
  `NETLINK_CAP_ACK` and `MSG_TRUNC`, already landed), 3 (`NLA_F_NESTED` as
  the sole malformation, already landed), 4 (op 9 keeps the coalesced
  `device`, with the `[]` restoration and the fail-noisy rejections), 5
  (`expect` on unsteered traces) and 6 (256 allowed IPs by accumulation, 32
  per `wg_set`, the label budget measured before the generator). No to 7
  (model `-EBUSY`) and 8 (anchor af_netlink.c): `-EBUSY`, `-EAGAIN` and the
  receive of a lone `NLMSG_DONE` stay explicit `unsupported` outcomes and
  N2-M13 is dropped. Reason: the smallest anchored surface outside WireGuard
  for a control-and-data mirror; the three af_netlink.c decisions would
  anchor code the mirror otherwise treats as the environment.
  Implementer's choices under them [AGENT, fork of the coordinator]: the
  receive of a start error's acknowledgement is in the domain (it carries
  the lookup's error code, which the start itself does not return; no
  WireGuard code runs, as for the receive of the chunk carrying the DONE); a
  stepped trace and the foreign-creator fixture exclude each other (both
  need descriptor 8); no check rule for the receive that runs no dump call
  (every socket operation reports the descriptor lookup's decisions, so the
  existing rules apply unchanged); `MAX_BRANCHES` stays 32768 (the 256-IP
  IPv6 trace measures 18,681 labels); the stepped socket's `netlink_autobind`
  draw (af_netlink.c:820, the collision with the fixture socket's port id)
  is a below-cut hidden site (id 170), consumed once at the first
  `wg_get_start`.
- **2026-10-12 [AGENT, fork of the coordinator]** The NET_RX placement rule
  covers the encrypt worker's ring poll: a pending NAPI poll runs at any
  worker's `ptr_ring_consume_bh` when the next record starts a NET_RX
  section (D2's placement (b), until now the decrypt worker's loop head
  only), because the kernel may switch from the decrypt worker's
  `cond_resched` to the encrypt kworker before ksoftirqd (w7_mixed under
  eight guests, design 17.17). Exact and fail-closed as before; no retry.

- **2026-10-13 [USER]** Proofs land on `main`, in a proof tree outside the
  mirror, once they hold over the mirror as it is on `main`: "If it lands
  clean, and the theorems are what we want, I think we should land it on
  main. Then Codex#2 as a follow on should figure out how to rebase on the
  updated mirror" (2026-10-12), refined the same day: "we should make the
  proofs run on the actual main-branch model first before landing it. That
  can be the next step - Codex#2 in a new worktree once the review comes
  back." The standing rule's new text (AGENTS.md: the proof tree, its gate,
  the lag-and-repair maintenance rule) is the coordinator's proposal under
  this decision and takes effect with the user's approval of the text at
  the landing of the carried-over spike.
- **2026-10-13 [USER]** `LEANUX_QEMU_SLOTS` is 8 as the standing value and
  the harness default, up from 3: "yes, that sounds reasonable, given we
  have more resources now", after four claim points ran at 8 on
  2026-10-12/13 with no guest-side disturbance.
- **2026-10-13 [AGENT, fork of the coordinator]** Review item 8
  (docs/2026-10-13-review-items-7-8.md, section 4), under the standing
  delegation: `jiffies` and the timer expiries are `UInt64` and compared by
  the C's `time_after` family written out (`Leanux/Kernel/Defs.lean`), the
  boot-clock birthdays `Int64` with the age test computed as the C's s64;
  the arm rule is split into the caller's read recovered from the record
  (`expires - delay`) and an environment admissibility condition on the gap
  to `mod_timer`'s read (negative: hidden mismatch; above one tick:
  `unsupported`, a stall); the age and counter tests declare their
  operands. No oracle change; no new decision (`dstCacheHit` deferred with
  the anchoring of `net/core/dst_cache.c`).
- **2026-10-13 [AGENT, coordinator]** Review item 8's counters stay `Nat`
  (its author's choice, endorsed): the operand evidence is delivered without
  the type change, and retyping would reach the proof tree's counter-window
  model under construction by the campaign.
- **2026-10-13 [AGENT, fork of the coordinator]** Review item 7, under the
  standing delegation (design section 10): the record-driven loop measures
  and the derived activation bound; the record-only kind-310 end-of-wait
  `jiffies` read over the explicit-fixture option for the firing window,
  written into the remote stream (the task's window closes before the
  waits), consumed by `idleTimers` and `afterAdvance`; the domain filter's
  turn bound named as its own (`DOMAIN_FILTER_TURNS`, `unsupported "runner
  budget: …"`), never an `invariant`; `Timing`'s constants kept for the
  filter's prediction only.
- **2026-10-13 [USER]** While the proof campaign runs, the mirror work is
  fidelity improvements, audits and the census's gaps rather than new
  targets: "let's plan to work on fidelity improvements / audit / census
  gaps while the proof campaign is running". The audits, in the order
  proposed and accepted: a mechanical mutation campaign against the
  check, a scratch oracle built at a different optimisation level to
  separate compiler-bound declarations from C semantics, correspondence
  audits of the oldest WireGuard modules by fresh agents, and a
  generated-trace soak with fresh seeds. New targets (the FIB trie, the
  timer wheel, KVM) wait.
- **2026-10-13 [AGENT, fork of the coordinator]** A mirror defect found by
  the device correspondence audit (docs/2026-10-13-audit-device.md, M1)
  and never exercised by the corpus: `setMtu` answered `-ERANGE` above
  `max_mtu` and nothing below zero where `dev_validate_mtu` answers
  `-EINVAL` for both (net/core/dev.c:9061-9075). Fixed with the cut's rule
  over the ioctl's int (the guest's `(int)op->a` applied in `Env.setMtu`),
  two traces at the arms (`w4_set_mtu_over_max`, `w4_set_mtu_negative`:
  semantic_mismatch before, agreement after, on s2), the trace field and
  the expected errno set corrected. With it the audit's X1
  (`wg_check_packet_protocol` decided from the packet, its error arm
  modelled and unexercised) and D1 (the handshake ring in `wg_destruct`'s
  guard, an invariant). The audit's other items stay as reported.
- **2026-10-13 [AGENT, fork of the coordinator]** The netlink correspondence
  audit's F1 (docs/2026-10-13-audit-netlink.md): the trace contract admitted
  a peer endpoint whose `af` and `len` present one family's bytes under the
  other `sockaddr` layout (family-4 bytes with `af` 10 and `len` 28, or
  family-6 bytes with `af` 2 and `len` 16), which `set_peer`
  (netlink.c:441-446) reads by `len` and `sa_family` alone and stores as an
  endpoint the mirror's parsed fields cannot express (the dump then
  differs). Closed fail-closed: the validator and `Runner.parseEndpoint`
  refuse exactly those two combinations; the ignored combinations of the W2
  design's 3.3 rows stay admitted; `corpus/netlink-controls` holds the two
  traces as expected rejections (`scripts/wg-netlink-controls.py`). A
  harness admission found by reading, never by a trace: the corpus had only
  the ignored combinations.
- **2026-10-13 [AGENT, fork of the coordinator]** Three defects of the
  receive path found by the correspondence audit
  (docs/2026-10-13-audit-receive.md), none ever exercised by the corpus,
  fixed on the mirror's side only: F1, `wg_packet_consume_data`'s `-ENOSPC`
  arm (receive.c:534-539) was an `invariant` stop and is the C's puts and
  silent free (`w7_ring_rx_1025`, held back from the tier suite: its 1024
  inline polls exceed the protocol's 64 ambiguous placements per trace); F7, `make_cookie`'s secret rotation
  (cookie.c:96-102) discarded the age test's outcome and is modelled from
  the records with the test a declared comparison
  (`e_underload_cookie_rotated`: the reply's bytes differed before); F6b,
  GRO's `rx_list` batch of 8 and the held lone TCP segment, where the
  mirror delivered everything at `napi_complete_done` (modelled,
  unexercised: the one-CPU kernel polls inline at every decrypt, so no poll
  holds 8 packets; `w7_multi_rx_9_rst_roam` was written for it and agrees
  under both mirrors, the endpoint-family decision marked repeatable). The exclusion
  reasons of the E design's §11 are corrected: the `> 2048` trylock arm is
  reachable since `wg_batch`/`wg_flood` but stays `unsupported` (the lock's
  state is unrecorded); the rotation is in. F10 (the handshake ring as a
  `List`) is deferred to its own task.
- **2026-10-13 [USER]** Kernel findings are filed in a tray: "We should adopt
  the 'tray' style of filing used in cerberus-lean amongst others. That
  is, **if** we find things in the kernel that might be of concern, we
  write a report in the repo for future analysis and filing."
  `docs/upstream-tray/` with its index, in the form of cerberus-lean's
  `lem-lean/doc/upstream-tray/` [AGENT, fork of the coordinator: the form
  copied, the states Draft/Filed/Withdrawn, reports only and no patch
  branches]. The rule is in AGENTS.md ("Kernel findings"). First entries:
  01 the send-side silent drops at a full encrypt ring or peer queue
  (`tx_dropped` untouched; the ring refuses consumed-but-uncleared slots),
  02 the receive-side silent drops at a full peer queue or decrypt ring
  (`rx_dropped` untouched, the free is `consume_skb`; the queue fills before
  authentication, put as a question).
- **2026-10-13 [AGENT, fork of the coordinator]** Claim-point robustness, three
  rules. (1) The encrypt worker's yield position is determined by
  elimination (`Leanux/Env/Batch.lean`, `cryptAhead`; W7 design 17.18):
  its loop reads no record per item, so when the records dispatch the tx
  worker at its yield and the tx section carries an item the mirror has
  not crypted (the per-item arm where the stop was expected), the
  suspended encrypt activation crypted it before yielding and one encrypt
  iteration runs there; fail-closed otherwise. The audit wave's tier
  failure was this, not a timer: site 100 is the arm record. (2) The
  protocol's ceiling on open NAPI placements is the trace's injected-
  message count (`evaluator/protocol.py`, `injected_messages`), one (c')
  placement per delivered data message, replacing the bound of 64; the
  receive-side 1025-item trace joins the tier. (3) `Q-M1-dispatch-order-
  ignored` has the inconclusive rule `D2-M12` has, from the recorded
  dispatch order (`evaluator/dispatch_orders.py`: a dispatch that was not
  the FIFO head with two pending distinguishes it); the sentinel subsets
  take several id prefixes. The replay tests' captures predate the kind-310
  record and the module had failed on every capture since item 7;
  `with_jiffies_end` appends the record as a replay fixture.
- **2026-10-14 [AGENT, fork of the coordinator]** The public claims are
  rewritten to the observation level, per the pre-release review
  (`docs/2026-10-14-pre-release-review.md`, sections 3, 4, 7, 9, 13, 14 and
  its limitations table): the README opens with the review's description
  (one configured, patched, single-CPU executable; selected supported
  traces; projected branch witnesses; operand presence; reconstructed
  scheduling choices; finite windows; separately pinned mirror theorems;
  neither the correspondence nor general security proved), carries a scope
  table of the consequential exclusions with their status and a
  trusted-boundary account; the proof register gains a result table
  (original claim, exact theorem, event boundary, premises, counterexample
  or blocker, pin) and counts theorem results, infrastructure and witnesses
  apart; the compiler experiment is renamed to witness-location stability
  with its units corrected; the tray's two drafts are narrowed to what was
  measured, with recorded loss, source-derived mechanism and attack
  feasibility separated; the reproduction guide names the approved build by
  identity. Sentences that describe the state after the review's code fixes
  are marked with the branch that carries the fix.
- **2026-10-14 [AGENT, fork of the coordinator]** Pre-release review finding
  11 (docs/2026-10-14-pre-release-review.md, section 11), the seccomp scope:
  `TSYNC` on the one-task group is in scope as the C's path (the thread walks
  of `seccomp_can_sync_threads` and `seccomp_sync_threads` meet only the
  caller; threaded synchronisation stays out, a representation limit);
  `instruction_pointer` is recorded at `populate_seccomp_data` (kind 312,
  record-only, class-approved, the oracle rebuilt at integration) and filters
  that branch on it are in the domain; EINTR, ENOMEM, ENFILE and the restart
  codes are ordinary `ERRNO` policy results, told from a guest failure by the
  trace's installs (provenance) in harness/linux.py, so the corpus and the
  generator emit them; the feature is named "single-task seccomp with
  classic-BPF translation and an interpreter service" with `BpfEngine`'s
  laws as premises; a sparse 4096-instruction single filter is deferred
  (the comparison child's record area), the reason in the design's section 10.
- **2026-10-14 [AGENT, fork of the coordinator]** `requireNotPending` is
  retired (a no-op; `docs/2026-10-11-dispatch-order.md`, the last section),
  the pre-release review's finding 3: with the section records and the
  scheduler loop the queued handshake send worker runs exactly where its
  section is, so a receive the kernel ran before it is determined; the stop
  excluded ordinary simultaneous initiation. Evidence: the receive-first
  captures of `p_sim_init_*` on s2, which the old mirror refused at
  peer.c:75 and the new one replays to each child's returns. The three
  batch traces stay outside the suites because the two guest children ran
  the unbound send worker and the receive worker in different orders, the
  harness's determinism rule (the review's finding 5), not the mirror's;
  the sequential one is in the `wireguard` suite.

- **2026-10-14 [AGENT, fork of the coordinator]** The pre-release review's
  checker findings 1, 3 and 5 (docs/2026-10-14-pre-release-review.md) are
  fixed in the evaluator and harness, not declared as limitations: (1) the
  boundary rule: every function of an anchored C file that an operation
  covers must be listed, branch-free, or a helper cut named in kcov.json
  with its reason (`helper_cuts`, 50 at this commit, classified by running
  the suites under the rule and reading the C); the old rule caught an
  unlisted function only on a declared span. One covered function is not
  cut because it owns choice points on a modeled path,
  `wg_socket_send_buffer_as_reply_to_skb` (the receive audit's F3): the
  cookie-reply trace fails the boundary rule until the mirror declares
  them, a mirror follow-on. (3) Every report carries the generated suites'
  selection account (candidates, in the domain, selected, rejection
  reasons over all candidates). (5) `operand_rows_distinct` beside
  `operand_pairs_matched`; and the `wg_observe` observation keeps arrival
  order within a peer session on both sides (a stable sort by peer key),
  where the global compact-JSON sort lost it. The one-off mutant of the
  observation (the sender's replies reversed, `Leanux/Env.lean`, run once
  on `d2_staged_flush_4` and deleted) was rejected as `semantic_mismatch`
  through the observation; under the old global sort the same mutant
  could not disagree. Found outside the directive, not fixed: under load
  `w7_multi_tx_2` can record the kernel queueing the transmit work twice
  (the robustness landing's schedule), which the mirror now accepts but
  `dispatch_problems` still reports ("a work item queued while already
  queued"); the schedule did not recur in the suite runs here.
- **2026-10-14 [AGENT, fork of the coordinator]** Pre-release review finding 2
  (docs/2026-10-14-pre-release-review.md, section 2): a peer timer's expiry
  is computed from the caller's own recorded `jiffies` read (kind 311,
  `kcov_timer_jiffies` on each of `mod_peer_timer`'s seven caller lines,
  record-only under the approved class; the s3 oracle pair) and compared
  with the arm record's published expiry, instead of recovering the read
  as `expires - delay`, which absorbed a delay wrong by one tick. The
  `mod_timer` read keeps its 0-or-1 admissibility against the caller's;
  the items 7-8 design's "publication identity" wording is withdrawn.
- **2026-10-14 [AGENT, fork of the coordinator]** Pre-release review finding 6
  (section 6): `Env.wgDelete` refuses a delete while a stepped dump is
  pending, as the guest does (`wg_delete_with_dump_pending`), since the
  mirror's dump cursor carries a Boolean device presence and not the C's
  retained device reference; the control `n6_delete_with_dump_pending`
  keeps the composition outside the domain (the campaign's stale-cursor
  witness was such an accepted replay). Supporting it means cursor
  ownership, the review's longer-term option, recorded in the W2 design.
- **2026-10-14 [AGENT, fork of the coordinator]** The receive-path scope holes of
  the pre-release review (`docs/2026-10-14-pre-release-review.md`, sections 8
  and 12, the IPv6 rate-limiting row): the under-load threshold declared with
  its operands and crossed exactly by `e_underload_511/512/513`; the flood
  summary checkable against the unsummarised execution (`LEANUX_FLOOD_EXACT=1`);
  the IPv6 ratelimiter table modelled (`.rlProtoIp6`, `table6`, a `wg_flood`
  with `family: 6`), the entry allocation's unrecorded site and the GC's
  exclusion written; `cookie.c:147` (`.macRatelimited`) and
  `wg_socket_send_buffer_as_reply_to_skb` (listed, five decisions) declared;
  `wgXmit` checks the packet header's destination against the environment's;
  the ECN rewrite's length implication asserted; the E arm named "cookie
  gating under the modelled load state"; disposition tables on both audits.
- **2026-10-14 [AGENT, fork of the coordinator]** The `cond_resched` in
  `default_device_exit_batch` (net/core/dev.c:12174, the device layer's
  pernet `exit_batch` inside `cleanup_net`'s section) is the ambient
  hidden site 427, passed over like `cleanup_net`'s own yield (152): two
  W8 traces met it under a loaded claim point as "choice kind 302 from an
  undeclared consumer" and passed alone (the integration record c047e64's
  named follow-on). Exact and fail-closed: the mirror runs nothing across
  it, a record there from any other site is still a mismatch, and no
  retry. Evidence: `W8_DEFAULT_DEVICE_EXIT` in `evaluator/test_model_replay.py`
  (the live capture with the record inserted; the old model fails, the new
  agrees) and the checker-level test in `evaluator/test_evaluation.py`.
- **2026-10-14 [AGENT, fork of the coordinator]** The mutation campaign's four
  reach findings (docs/2026-10-13-mutation-campaign.md, section 8) closed as
  check rules and one declaration, no mirror semantics changed: (1) `iput`
  is a listed decision function with `iput.last_reference` (fs/inode.c:1895)
  and `iput.lazytime_dirty` (:1896) declared, the pipefs inode's count
  deciding it and `iputReport` saying which way the C goes where the mirror
  holds no inode (the shared anonymous inode keeps its pinned reference; a
  socket's or a pin's inode is freed), so a leaked inode is seen against
  iput_final's coverage, on the new trace `p_close_both_ends` (no pipes trace
  closed both ends inside its operations before); (2) two distinct declared comparisons at one
  condition line must match distinct kernel comparison PCs, a C comparison
  being an instruction; (3) the decision table declares terminal outcomes (the arms at
  which the C function returns), and a decision reported after one at a
  later line of the function is a decision evaluated past Linux's return;
  a line-level rule was tried twice and withdrawn, a line owning several
  blocks; (4) the operand relation on the
  main path is section-confined: a branch the mirror stamped with NET_RX
  ordinal k matches only the records of the guest's k-th `net_rx_action`
  block, on every trace, so a mis-stamped mirror fails where before only
  the placement evidence (run on a first-run mismatch) could see it. The
  disagreement that had kept the confined relation off the main path
  (w7_mixed op 4, the mirror's ordinal 4 against the guest's 6) was the
  mirror's: it counted only the NET_RX sections it runs as a worker, while
  the guest numbers every `net_rx_action` section, including the loopback
  transmissions' and the flood producers' sections the mirror consumes and
  skips; now every consumed section start advances the ordinal
  (`noteNetRxStart`, at the four consumption points), an instrument
  change, no data or control flow of the C. The narrow form tried first
  (4ca380f: the placement evidence forced for every trace with open
  placements) left the mutant alive on rx_counter_jump, which has no open
  placement, and is withdrawn; the evidence runs on a first-run mismatch
  again, the W7 13.2 (ii) form. Each mutant is rejected after its fix; the
  area suites agree.
- **2026-10-14 [USER]** The Lean toolchain moves to v4.35.0: "If we can bump
  to 4.35 we probably should, we can then also use the new lake comparator
  feature"; "we can update our lean toolchain if need be". The bump is on
  `main` only; the proof campaign's worktree keeps v4.33.1 until it merges
  [USER: "Just make sure not to break the Codex#2 grind"], which
  `scripts/in-bundle`'s per-checkout toolchain selection makes safe. The
  one source change v4.35.0 needs is a type ascription in
  `Leanux/WG/NetlinkDump.lean` (no behaviour change). Kraken (`.deps/kraken`
  at 8af7806) builds on v4.35.0 and not on v4.33.1, which is the reason
  for the version [AGENT, coordinator: the toolchain tests of 2026-10-14].
- **2026-10-14 [USER]** Rule Zero's canonical form, for every proof charter
  and the standing rules: "(1) the mirror might be wrong, (2) the kernel
  might contain bugs, (3) the former is much more likely than the latter."
- **2026-10-14 [USER]** The binary-level adequacy of the WireGuard mirror
  and the transport of its landed results to the binary are the objective
  of the simulation track; the theorem and its trust surface must be
  correct and are reviewed independently; everything outside the trust
  surface is a means, ephemeral unless later promoted: "The eventual
  adequacy result & transport of wireguard results to the binary, is the
  only thing that matters. We are going to get it done by any means
  necessary. The theorem / trust surface MUST MUST be correct. Everything
  else is ephemeral." The method is a direct per-region grind, not a
  reusable checker (same day: "we're not building some reusable toolchain,
  we are proving a single target theorem"). Charter:
  docs/2026-10-15-charter-binary-adequacy.md.
- **2026-10-14 [USER]** The direction of discrepancies at the binary level:
  "the purpose of the verification should be to validate the mirror, and
  detect discrepancies. Not to conform to mistakes in the mirror. The
  binary (ie the real kernel) is the source of truth here of course." A
  region that will not close because the mirror differs from the machine is
  a mirror defect fixed on the mirror lane; the adequacy theorem's
  precondition and relation are never narrowed to accommodate one. First
  instance: the index lookup's dead-peer store (peerlookup.c), found by the
  grind at milestone 1 [AGENT: the fix on task/index-lookup-fix].
- **2026-10-14 [AGENT, fork of the coordinator]** The index hashtable has the
  C's shape: a hashed entry is its index and its owner (`IndexOwner`: a
  peer's handshake or a keypair, the structures the entry is embedded in,
  noise.h:30-31, :65-66), and the entry's one peer word lives in the owner
  (`Peer.handshakeEntryPeer`, set at noise.c:68; `Keypair.peer`, set from
  the handshake's word at noise.c:107, :827). `indexLookup` reads the word
  through the owner and stores `wg_peer_get_maybe_zero`'s result back into
  it (peerlookup.c:218), so a failed get leaves NULL there, a later lookup
  of the same entry takes the get's `!peer` arm (peer.c:75), and the owner's
  other reads of the word (`PACKET_PEER(skb)`, `wg_peer_get(keypair->entry.peer)`,
  `entry.peer->device->index_hashtable`) find NULL: each is an explicit
  fail-closed arm (`IndexOwner.peerDeref`, `unsupported`), where the C
  dereferences a NULL pointer, never a default. Before, the table entry
  kept its own copy of the peer id and the keypair a second one
  (`Keypair.peer : PeerId := 0`), two words the C does not have: a mirror
  defect found by the binary adequacy grind's region lemmas over
  `wg_index_hashtable_lookup`, the first Rule Zero finding at that level,
  fixed in two steps (the store-back into the table's copy, then the
  aliased word). Witnesses (a hashed entry of each owner naming a peer at
  count zero, looked up twice, then the owner's word dereferenced): the
  mirror on main reported `peerGetMaybeZeroDead` at both lookups and went
  on through the dereference; the fixed mirror reports
  `peerGetMaybeZeroDead` then `peerGetMaybeZeroNull`, the C's order, and
  stops at the dereference. The arms are modelled and unexercised on this
  configuration (one CPU, no preemption): no lookup finds an entry whose
  peer is at zero, the reasons with the C lines in the lifecycle design
  (16.6). Not a scope cut. The Peer audit's F2 (the mirror erases a peer at
  count zero where the C frees it at `rcu_release`) is not a mirror change:
  the adequacy theorem quantifies over states the relation names, reachable
  or not, and the fixed mirror handles a constructed zero-count state as
  the C does; the erase-versus-free divergence is for the simulation
  relation to abstract (an unreferenced object relates to its absence),
  on the claim, with its C lines in the lifecycle design (16.6), that no
  modelled path reads a peer between the zero and the release. The mirror
  stays deterministic; a modelled reader found later would make it a
  record-only RCU-callback section, reported rather than built.
- **2026-10-14 [USER]** Use the box aggressively: "we can share guidance with
  the agent to be more aggressive with resources where this would speed them
  up". The guest-slot default moves from 8 to 16 (the box has 32 cores and
  over 90 GB free most of the day; guests are single-threaded; the measured
  claim point of 2026-10-14 took 2 h 17 min at 8 slots on a shared box);
  builds and suite runs run concurrently across agents; `capped`, the
  memory cap, the KILLED-is-failure rule and the one-recorded-rerun rule are
  unchanged [AGENT, coordinator: the measurement and the number].
- **2026-10-15 [USER]** The mirror's state is split into per-subsystem
  worlds, each subsystem operating over its own localized world type
  (WireGuard, the file layer, seccomp, the task lifecycle, with the record
  stream, the decision log and the dispatch bookkeeping as the ambient part
  every module has; the runner holds the product and is the only composer).
  Two kinds of framing: structural, enforced by the types and free, because
  a function that is not passed a piece of state cannot affect it in a
  program without side effects; and non-localizable, needing footprint
  invariants, kept only where an effect cannot be localized. The design:
  docs/2026-10-15-design-state-split.md.
- **2026-10-15 [USER]** Functions are narrowed at the type level to the data
  they access, wherever that is cheap: within
  WireGuard the leaves (the trie, the rings and queues, the index table and
  slots, the cookie and rate-limiter functions, the timer operations) take
  their field group's type; the entry points keep the WireGuard world. No
  footprint invariants in this stream.
- **2026-10-15 [USER]** The retrofit is compile-driven, with no compatibility
  wrappers and no equivalence lemmas: narrowing a type deletes fields from
  a function's view, which cannot change behaviour in a program without side
  effects, so the types are changed and whatever fails to typecheck is
  repaired. In the proof tree, a statement that mentions the global World is retyped
  over the local world; a frame lemma the types or the one lift lemma now
  give is deleted, even if its old proof would still compile; nothing is
  re-proved.
- **2026-10-15 [USER]** Timing against the campaigns: Codex#2's campaign 1
  (`proofs/campaign`) finishes R3 and R4 and lands, its retrofit one job
  afterwards; Codex#1's campaign 2 (`proofs/campaign-2`) stops at its
  checkpoint now and resumes on the split mirror; Codex#3's binary adequacy
  grind continues, its R a relation over the WireGuard world literally. The
  split starts when B3 is on `main` and lands before lane C's C1, whose new
  module retypes then [AGENT, coordinator: the sequencing argument; the
  measurements in the design note].
- **2026-10-15 [AGENT, fork of the coordinator]** B4 part 1 (the settled
  parts of docs/2026-10-15-design-b4-load-ratelimiter.md): the ratelimiter
  entry allocation is a kind-305 site consumed by `rlAllocFail`, with the
  E design's "not in the hook's list" sentence corrected (the hook is
  generic); `wg_ratelimiter_init`'s three allocation arms are constant
  false with the reason (creation allocations outside the model, census
  row 132 unchanged); the uninit walk empties both ratelimiter tables, as
  the C does, with `l_delete_ratelimited6` and `l_recreate_ratelimited6`
  as witnesses; the producer's busy arm (receive.c:554) produces under the
  trylock, constant on this configuration (spinlock_up.h:56), with
  `e_underload_busy` (2,100 packets). The GC stays excluded; its reason is
  sharpened in the note's section 3 and the claim that the guest's
  per-operation remote reset is a silent instrument gap is retracted
  (`section_problems` fails a lost section loudly).
- **2026-10-15 [AGENT, fork of the coordinator]** B4 part 2, the prototype
  that precedes the user's U1 decision (docs/2026-10-15-design-b4-load-
  ratelimiter.md 2.3, 13): the flood runs exactly over `Env.batch`'s
  machinery; the summary, the discard, the exact flag and the checker's
  `wg_flood` arm are deleted; the three checker rules of U1 are changed,
  with the `repeatable` list grown by three consume-path decisions the
  prototype run found (`consumeFlood`, `consumeFailedPut`, `hsInitNoPeer`);
  `make_cookie.ipv4`'s witness corrected to the built kernel's layout (a
  declaration error the skipped flood had hidden); `e_underload_merged`
  kept with its new detail. The user accepts or drops this part as U1.
- **2026-10-15 [USER]** The representation batch: B4's U1 accepted (the flood
  runs exactly over `Env.batch`; the summary contract, the discard, the exact
  flag and the checker's flood special case are deleted; the three checker
  rules change as the B4 note names, with the `repeatable` list the run
  found); B2 (the second device) is held until campaign 1 lands, its design
  and review kept, for the proof carry the review costed at 10 to 15
  agent-days. "2,3,4 agree with recommendation" [AGENT, coordinator: the
  recommendations].
- **2026-10-15 [USER]** B3, the timer wheel as a mirror: "Agree re B3, go
  ahead as proposed". The environment line moves (U1: the firing set and
  order become semantics in both directions, E1 over stream-bounded passes;
  the tick's placement, the wait's tick count and the base clock stay
  recorded; the kind-310/311 reads are not made derived); two record-only
  hooks (U2: kind 313 in `__mod_timer` after the forward on both paths, kind
  314 in `enqueue_timer`, written without steering under `base->lock`,
  carrying the timer's address; class-approved as record-only, the new
  oracle pair's identity recorded at the landing); `kernel/time/timer.c`
  mirrored but unanchored, its hooks may add lines (U3); the deferral case
  `unsupported` only with the lookahead (U4); the per-timer layout with an
  enqueue stamp (U5) [AGENT, fork of the coordinator: the design; the
  Claude Opus 5.5 review at 6fe87f2].
- **2026-10-15 [USER]** The simulation relation `R` of the binary adequacy
  charter is minimal, a frame property: exactly what the simulation needs,
  over the WireGuard projection of the World, each clause justified by an
  anchored function's read or write or by a field a landed result observes;
  everything a function does not touch is a frame theorem, never a relation
  clause ("surely it's actively bad for the invariant to carry a load of
  gunk that relates states that don't matter. Morally, we want to strip the
  relation to exactly what the simulation needs (that's a kind of frame
  property)"; "the right way to prove the theorem is minimally").
  Definitions built for state outside `R` are parked under `binary/attic/`,
  off the proof path, for a possible later milestone. The charter's first
  wording ("relates the whole mirror world") was the coordinator's error,
  read literally by the grind [AGENT, coordinator]; the amendment is in the
  charter's section 1.
- **2026-10-15 [USER]** Lane C, the anchoring question (design note U1):
  `fib_frontend.c`, `fib_semantics.c` and `route.c` are anchored with cut
  lists and the per-caller cut for the helpers IPv6 shares, in C2 and C3.
  This revises the boundary decision of 2026-10-07 for routing (the line is
  now drawn by function name in the cut lists, one layer down, under that
  decision's own "unless this breaks important things": campaign 3's
  end-to-end routing composition) and reverses the `ip_error` deferral of
  2026-10-08 (the input corpus reaches it). "Agree on the anchoring
  question."
- **2026-10-15 [USER]** Lane C, IPv6 (design note U2): deferred, "might be a
  task later"; IPv6 routing stays environment, and campaign 3's routing
  composition is stated for IPv4 in its charter.
- **2026-10-15 [AGENT, coordinator]** Lane C's tactical decisions as the
  revised note recommends: three landings with C1 first (U3); the
  `hash_mix` global-hash walk treated as a decision cut (U6).
- **2026-10-15 [USER]** Lane C, the module's home and the standing rule
  (design note U4 and U5): the FIB module lives at `Leanux/Net/` beside
  `FS`, `WG` and `Seccomp`, and AGENTS.md's list of the mirror's directories
  gains `Leanux/Net` ("agree with recommendation").
- **2026-10-15 [USER, through the coordinator]** Lane C, a check-rule change
  on the trust surface: a `wg_batch` operation is compared against the
  WireGuard files, the headers they inline and `net/ipv4/fib_trie.c`
  (`evaluator/check.py`, `BATCH_FILES`), since the batch's sends run the
  trie's lookups and an anchored file's in-window coverage is witnessed in
  a batch as in a single operation. Its one-off mutant
  (C1-M8-batch-lookup-outcome) was rejected once and removed.
- **2026-10-15 [AGENT, fork of the coordinator]** The W7 tier's receive
  twin under load: the mirror's bound of 8 on the NAPI placement vector
  (`napi_irq_before_put`) was a budget from when open placements were
  rare, inconsistent with the protocol's ceiling (the injected-message
  count, 2026-10-13); under load the twin opens 1,018 placements and the
  kernel takes (c') at a few, so the check's before-put run was refused and
  the trace failed at two claim points. The mirror's ceiling is the
  records' NET_RX section-start count (exact, fail-closed); the selection
  rule is unchanged (the kernel's comparison rows decide each poll's
  placement, replayed once as the evidence); `section_agreement` costs the
  section's records per poll. Not a retry, not a widened enumeration.
- **2026-10-15 [USER]** The two heavy B4 traces are dropped: `l_recreate_ratelimited6`
  (the recreate witness) and `e_underload_busy` (the busy arm). Their comparison
  child sits at the guest's 4.5 s rekey bound on both oracles (4.28 s and 4.40 s
  alone; over it beside any other suite), a fixture property under TCG that no
  reshape changes, measured by the B3 fork on s4 and s5 (B3's hooks add four
  records); `l_delete_ratelimited6` stays as the two-table uninit witness and the
  busy arm keeps its constant-false declaration. "(1) agreed" to the
  coordinator's recommendation. The structural remedy for the class (113 of 341
  traces run past half the bound in the comparison child) is KVM acceleration of
  the guest, a fixture case to put separately [AGENT, coordinator].
- **2026-10-15 [USER]** B3 and C1 land as one integration ("(2) great, let's land
  it"), after one claim point on the combined head on the s5 pair.
- **2026-10-15 [AGENT, coordinator]** C1 lands before the state split, not after as
  the split's decision entry said: C1 finished in one session instead of the
  estimated ten days, and its new module retypes cheaply at the split since
  nothing depends on it yet.
- **2026-10-16 [AGENT, fork of the coordinator]** Superseded detail of the
  state split: the task state split by task id into three per-subsystem
  tables (a file-layer part, a seccomp part, a signal-and-lifecycle part)
  and the separate "task lifecycle" world named in the 2026-10-15 entries
  were the coordinator's detail, not the user's decision, and are withdrawn:
  Codex#4's independent review (task/review-state-split, 7b70875) showed
  that `pipeWrite`'s SIGPIPE, `fput`'s task tests and the seccomp filter's
  `forceSigSeccomp` reach the task's signal state inside mirror functions at
  the C's call sites, so sibling task worlds hit the design's own stop risk
  with certainty. Revision 2 of docs/2026-10-15-design-state-split.md keeps
  one shared task store under a `TaskM` layer that the file layer and
  seccomp stack on. The user's decisions (localized worlds, narrowing where
  cheap, delete fields and see what breaks, the campaign order) stand.
- **2026-10-16 [AGENT proposal, from Codex#4's review; pending the user]**
  The one exception to the rule that the runner holds the product and is
  the only composer: subsystem operations may call the shared task and signal
  services at the C's existing call sites (a pipe's SIGPIPE inside
  `pipeWrite`, a trap's signal inside `seccompFilter`, the task-work test
  inside `fput`); the runner alone assembles the full product and
  orchestrates operations across independent stores (the syscall dispatch,
  the environment model, the seccomp child probe and trap return). Put to
  the user because it qualifies their formulation.
- **2026-10-16 [AGENT proposal, from Codex#4's review; pending the user]**
  The state split's mirror landing carries reported proof lag under the
  standing lag-and-repair rule, and the proof tree it retrofits is campaign
  1's landed tree (7,405 theorems on 2026-10-16), as one follow-on job with
  its own proof gate and signoff, not a green proof gate over `main`'s
  1,399-theorem tree at the landing, which the campaign order the user chose
  makes impossible. Revision 1's promise of a green gate at the landing is
  withdrawn.
- **2026-10-16 [USER]** The state split's composer rule: the overriding aim is
  to reflect the actual Linux decomposition of state, and composition points
  are added where they exist in Linux. So
  the file layer, seccomp and the signal paths call the shared task services
  at the C's own call sites, below the runner; the proposal of revision 2 is
  adopted with that principle as its rule.
- **2026-10-16 [USER]** The split's mirror lands with its proof lag reported,
  and the landed campaign-1 tree is the retrofit's baseline with its own gate
  and signoff.
- **2026-10-16 [USER]** No proofs and no proof gate on `main` until campaign 1
  lands, removed at the end of the split: the prototype proof tree on `main` (`Leanux/Proofs/`, the replay-window
  result and the layers it rests on, 1,399 theorems: a prototype for
  campaign 1 that landed on `main` by sequencing and should not have been
  there) and its
  gate are removed from `main` at the state split's cutover until campaign
  1 lands: `Leanux/Proofs/`, `Leanux/Proofs.lean`, the `LeanuxProofs` lake
  target and `scripts/proof-gate` itself deleted (no erroring stub, no
  notice); AGENTS.md's proof-gate paragraph and the proof-tree commands in
  its build-and-check and gates sections removed as a consequence of the
  deletion, while its standing rule stays (theorems live only in the proof
  tree, Rule Zero, no theorem is an acceptance gate; the gate text returns
  with campaign 1's landing, as that landing's own change); the register's
  rows and lag notes for the prototype removed, its map and the campaign
  rows kept. The binary track's gate (`proof-gate --binary`, which lives
  on `task/binary-tv`, not on `main`) is not a proof-tree gate and moves
  into its own script (`scripts/binary-gate`, nothing else in it) at that
  branch's merge, since the binary claim point still needs it. Not a
  standing rule: a refactor correcting an accident of sequencing [AGENT,
  coordinator: the cutover steps].
