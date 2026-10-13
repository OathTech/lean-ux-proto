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
