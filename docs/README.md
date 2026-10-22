# Documentation guide

Start with the [project overview and health warning](../README.md). For a
first run, follow [REPRODUCING.md](../REPRODUCING.md). This directory contains
both maintained reference documents and dated research reports. A charter is
a target, not a completed result; a historical passing run applies to the
revision and scope it names.

## Choose a starting point

| If you want to… | Read |
| --- | --- |
| Understand what a passing comparison means | [Correspondence guide](../correspondence/README.md): observations, branch/operand witnesses, scheduling reconstruction and gaps |
| Assess a theorem claim | [Proof register](proofs.md#results): statements, premises, mirror pins and current/lagging status |
| Understand the three proof campaigns | [Campaign 1](2026-10-13-proof-campaign.md), [Campaign 2](2026-10-14-proof-campaign-2.md), [Campaign 3](2026-10-18-proof-campaign-3.md); use the register for subsequent repairs |
| Evaluate the link to compiled Linux | [Binary experiment](../binary/README.md): function/component results, trust premises and the saved-ELF requirement |
| Read the strongest concerns | [Scope review](2026-10-20-fresh-eyes-scope-review.md), [bounded probes](2026-10-21-proof-probes.md) and [pre-release review](2026-10-14-pre-release-review.md), with their dates and dispositions |
| Inspect potential kernel findings | [Report tray](upstream-tray/INDEX.md): draft observations and questions, with the evidence level for each |
| Reuse an existing environment | [Offline usage](offline-usage.md) |
| Contribute or understand project direction | [Working rules](../AGENTS.md), [worktrees](worktree-practices.md) and [decisions](decisions.md) |

The [decision census](2026-10-13-decision-census.md) measures declared mirror
choices, not an independent enumeration of every C choice. The
[compiler experiment](2026-10-13-compiler-experiment.md) examines witness
stability across optimization levels, not semantic equivalence. Source audits
of [device](2026-10-13-audit-device.md),
[handshake](2026-10-13-audit-handshake.md),
[receive](2026-10-13-audit-receive.md) and
[netlink](2026-10-13-audit-netlink.md) are dated reviews, not completeness proofs.

## Reference documents

| Document | Contents |
| --- | --- |
| [decisions.md](decisions.md) | Decisions with dates and provenance |
| [proofs.md](proofs.md) | Claim register, proof-tree map and result maintenance |
| [upstream-tray/INDEX.md](upstream-tray/INDEX.md) | Report drafts and their evidence/status |
| [2026-10-11-interface.md](2026-10-11-interface.md) | Wire opcodes, record kinds, site IDs and fixture flags |
| [worktree-practices.md](worktree-practices.md) | Shared inputs, private outputs and cleanup |
| [offline-usage.md](offline-usage.md) | Staged dependencies and offline use |
| [2026-10-22-setup-findings.md](2026-10-22-setup-findings.md) | Setup defects, repairs and reproduction commands for maintainer follow-up |
| [nono-profile-proposal.md](nono-profile-proposal.md) | Devbox-specific sandbox proposal; not a prerequisite for ordinary setup |

## Dated designs and reports

The tables below index development history. Counts, exclusions, pending gates
and branch statuses belong to the document's stated checkpoint unless a later
correction is recorded. Use the guides above for current setup and claim scope.

## Plans and strategy

| Document | Contents |
| --- | --- |
| [2026-09-29-way-forward.md](2026-09-29-way-forward.md) | The assessment that set the thin-layer direction: a behavioural mirror, no theorem proving, data and control-flow correspondence |
| [2026-09-29-next-plan.md](2026-09-29-next-plan.md) | Finish the FD/eventfd slice, then WireGuard; superseded by the kernel scout (2026-10-12) and the decisions register for what followed |
| [2026-10-03-choice-stream-strategy.md](2026-10-03-choice-stream-strategy.md) | Hidden inputs recorded at generic kernel interception points and replayed: the choice stream |
| [2026-10-03-hidden-inputs-design.md](2026-10-03-hidden-inputs-design.md) | The hidden-input record kinds and their sites |
| [2026-10-03-steering-design.md](2026-10-03-steering-design.md) | Steering a hidden input to a chosen outcome; the kernel mechanism later superseded |
| [2026-10-06-contended-host.md](2026-10-06-contended-host.md) | Check failures on a contended host, and the rule that a scheduling-dependent failure is a modelling gap, never a retry |
| [2026-10-06-future-proof-paths.md](2026-10-06-future-proof-paths.md) | Cheap conventions that keep later proof work possible without doing it |
| [2026-10-08-pause-state.md](2026-10-08-pause-state.md) | What was on main and on branches at the October pause; historical |
| [2026-10-11-dispatch-order.md](2026-10-11-dispatch-order.md) | Recording which queued work unit a section runs, at the source |
| [2026-10-12-kernel-scout.md](2026-10-12-kernel-scout.md) | Candidate next mirror targets scored; epoll and seccomp chosen |
| [2026-10-12-simulation-target-review.md](2026-10-12-simulation-target-review.md) | Whether the mirror is a suitable target for a later simulation proof: suitable with named representation changes, since landed |
| [2026-10-15-state-split-companion.md](2026-10-15-state-split-companion.md) | Proposed revision of the state split after independent review: shared task services, localized worlds, cheap leaf narrowing and staged proof repair |
| [2026-10-14-wireguard-parallel-plan.md](2026-10-14-wireguard-parallel-plan.md) | Historical sequencing plan for representation changes, mirror extensions and proof carries |
| [2026-10-15-review-state-split.md](2026-10-15-review-state-split.md) | Independent review of the state-split design, footprint evidence and proof-migration scope |

## WireGuard

| Document | Contents |
| --- | --- |
| [2026-09-30-wireguard-stage-a-report.md](2026-09-30-wireguard-stage-a-report.md) | Stage A report: configuration and device state; its scope and exclusions are superseded by the WireGuard census (2026-10-06) and the decision census (2026-10-13) |
| [2026-09-30-wireguard-stage-b1-report.md](2026-09-30-wireguard-stage-b1-report.md) | Stage B1 report: transmit and routing; scope superseded as above |
| [2026-10-01-wireguard-stage-b2-report.md](2026-10-01-wireguard-stage-b2-report.md) | Stage B2 report: the receive path up to Noise; scope superseded as above, and the receive audit (2026-10-13) is the current reading of that path |
| [2026-10-01-wireguard-stage-c-report.md](2026-10-01-wireguard-stage-c-report.md) | Stage C report: the Noise responder; scope superseded as above, and the handshake audit (2026-10-13) is the current reading |
| [2026-10-04-d1-sprint.md](2026-10-04-d1-sprint.md) | D1: the initiator role, in parallel streams |
| [2026-10-04-d2-data-plane.md](2026-10-04-d2-data-plane.md) | D2 design: the data plane, workers and queues |
| [2026-10-04-d2-sprint.md](2026-10-04-d2-sprint.md) | D2 sprint record |
| [2026-10-05-d3-timers.md](2026-10-05-d3-timers.md) | D3: timers, timer sections and virtual time |
| [2026-10-05-a-alloc.md](2026-10-05-a-alloc.md) | A: allocation outcomes recorded and steered |
| [2026-10-05-e-dos.md](2026-10-05-e-dos.md) | E: cookies and rate limiting under load; historical exclusions were revised later. IPv6 rate limiting is now modeled; periodic GC remains excluded |
| [2026-10-05-e-probe-results.md](2026-10-05-e-probe-results.md) | E: the under-load reachability probe |
| [2026-10-05-l-lifecycle.md](2026-10-05-l-lifecycle.md) | L: device lifecycle |
| [2026-10-06-wireguard-census.md](2026-10-06-wireguard-census.md) | Coverage census of WireGuard's source against the mirror; the W rows |
| [2026-10-06-w1-w2-netlink.md](2026-10-06-w1-w2-netlink.md) | W1 and W2: netlink completeness and multi-message dumps |
| [2026-10-06-w3-w12.md](2026-10-06-w3-w12.md) | W3 and W12: two small coverage workstreams |
| [2026-10-06-w4-w7-transmit-bulk.md](2026-10-06-w4-w7-transmit-bulk.md) | W4 and W7: transmit shapes and bulk queues; the two-drop finding it left open is closed in the full-ring tier document (2026-10-13), and its 17.16 counterexample is superseded there |
| [2026-10-06-w5-w6-receive.md](2026-10-06-w5-w6-receive.md) | W5 and W6: receive shapes and the stack's reactions to inner packets |
| [2026-10-06-w8-w9-netns-routing.md](2026-10-06-w8-w9-netns-routing.md) | W8 and W9: netns exit, socket errors and routing |
| [2026-10-13-w7-full-ring-tier.md](2026-10-13-w7-full-ring-tier.md) | The W7 full-ring tier: the two silent drops at the 1024-item wrap explained from the records (two uncleared carried slots, no interleave), the tier's five traces |
| [2026-10-13-review-items-7-8.md](2026-10-13-review-items-7-8.md) | Review items 7 and 8: the runner's budgets as derived or record-driven measures with the kind-310 end-of-wait read, and jiffies as the C's 64-bit type with its comparisons declared; its section 4's "publication identity" claim for the arm rule is corrected by the pre-release review's finding 2 (the caller's read is recorded, after the fix on task/review-timer) |
| [2026-10-13-audit-device.md](2026-10-13-audit-device.md) | Correspondence audit of `Leanux/WG/Device.lean` against device.c by a fresh reader: 13 items, one observable (the MTU error code), fixed |
| [2026-10-20-fixed-width-audit.md](2026-10-20-fixed-width-audit.md) | Fixed-width kernel integers held as naturals: the allowed-IPs `seq`, `device_update_gen` and `rt_genid` retyped as words after the binary track's executed comparison found the first; the rest declared or shown equal |
| [2026-10-13-audit-handshake.md](2026-10-13-audit-handshake.md) | Correspondence audit of `Leanux/WG/Handshake.lean` against noise.c: nine internal items, none observable; two fixed |
| [2026-10-13-audit-receive.md](2026-10-13-audit-receive.md) | Correspondence audit of the receive path against receive.c and cookie.c: 14 items, two observable (the receive ring-full drop, the cookie secret rotation), fixed; residual items F2, F3, F12, F13 open |
| [2026-10-13-audit-netlink.md](2026-10-13-audit-netlink.md) | Correspondence audit of the netlink modules against netlink.c: one observable data-shape item (endpoint bytes by family), closed fail-closed |
| [2026-10-13-decision-census.md](2026-10-13-decision-census.md) | The decision census: 1382 decisions and their outcomes by anchored file, every exclusion in force with its justification, the anchored-file boundary, the W13 scope; its denominator is declared mirror decisions, not independently enumerated C choices |
| [2026-10-13-compiler-experiment.md](2026-10-13-compiler-experiment.md) | Witness-location stability across two optimisation levels of GCC 13.3: what refused the size-optimised image and what the static comparison shows; not evidence about the C's semantics |
| [2026-10-13-mutation-campaign.md](2026-10-13-mutation-campaign.md) | The mutation campaign: 308 sampled mechanical mutants of the mirror against the check on s2 (`scripts/mutate.py`), every survivor classified (equivalent projection, logging-only, corpus boundary, real), four check-reach findings, the channels' shares; power kept apart from presence |
| [2026-10-15-audit-peer.md](2026-10-15-audit-peer.md) | Source audit of peer lifetime, removal and lookup paths against peer.c and peerlookup.c |
| [2026-10-15-audit-send.md](2026-10-15-audit-send.md) | Source audit of transmit, queueing and handshake-send paths against send.c and its callees |
| [2026-10-15-design-b1-handshake-ring.md](2026-10-15-design-b1-handshake-ring.md) | Handshake PtrRing design, probe evidence and dispositions of its independent review |
| [2026-10-15-design-b1-review.md](2026-10-15-design-b1-review.md) | Independent review of the handshake-ring design and its evidence plan |
| [2026-10-15-design-b3-review.md](2026-10-15-design-b3-review.md) | Independent source review of the timer-wheel design |
| [2026-10-15-design-b3-timer-wheel.md](2026-10-15-design-b3-timer-wheel.md) | Timer-wheel design and the proposed boundary between kernel and environment modeling |
| [2026-10-15-design-c-review.md](2026-10-15-design-c-review.md) | Independent review of the IPv4 FIB trie design and its probe evidence |

## Pipes, epoll and seccomp

| Document | Contents |
| --- | --- |
| [2026-09-29-fd-eventfd-slice-report.md](2026-09-29-fd-eventfd-slice-report.md) | The file-descriptor and eventfd slice, final report |
| [2026-10-05-pipes-reconnaissance.md](2026-10-05-pipes-reconnaissance.md) | Pipes as the scale test, reconnaissance |
| [2026-10-05-p-pipes.md](2026-10-05-p-pipes.md) | P: pipes stage 1 design, including the signal decision P9 |
| [2026-10-12-epoll-design.md](2026-10-12-epoll-design.md) | Epoll over the FS slice: design v2 with its independent audit and audit response; landed 2026-10-13 |
| [2026-10-12-seccomp-design.md](2026-10-12-seccomp-design.md) | Seccomp as a single-task mirror with the eBPF engine as a service: design v2 with its independent audit, audit response and the user's config case (approved 2026-10-13) |

## Proofs

The landing reviews of [Campaign 2](2026-10-20-review-campaign-2-landing.md)
and [Campaign 3](2026-10-20-review-campaign-3-landing.md) explain the scoped
claims and repairs. Campaign 2's follow-on closes the H5 pending-unit boundary
claim; Campaign 3's T4/T5 still have unconstructed premises.

The [binary landing report](2026-10-19-binary-landing-assessment.md) records
the paired experiment's carry to the split mirror and pinned s5 image, its
separate build/gate and runtime validation, and the open milestone-1 review
obligations. Current setup commands are in [binary/README.md](../binary/README.md).

| Document | Contents |
| --- | --- |
| [2026-10-21-proof-probes.md](2026-10-21-proof-probes.md) | Three bounded probes after Campaign 3: outcomes, evidence limits, validation and reproduction |
| [2026-10-21-lifetime-fault-probe.md](2026-10-21-lifetime-fault-probe.md) | Open initialized fault-exclusion goal and a checked local countermodel; not an initialized counterexample or a new security guarantee |
| [2026-10-21-observer-removal-probe.md](2026-10-21-observer-removal-probe.md) | Removing one getter event breaks its unchanged coverage equation; erasure and safety of the retained history survive |
| [2026-10-21-independent-input-probe.md](2026-10-21-independent-input-probe.md) | Independent fixed input sample and single-CPU interference audit; initialized race reachability remains unproved |
| [2026-10-12-charter-window-proof.md](2026-10-12-charter-window-proof.md) | The first proof charter: replay freedom of the receive counter window, Rule Zero, the layered models |
| [2026-10-12-spike-window-review.md](2026-10-12-spike-window-review.md) | The independent review of the spike, in two parts: the original and its carry-over onto the new mirror |
| [2026-10-13-spike-window.md](2026-10-13-spike-window.md) | The spike's own report |
| [2026-10-13-spike-window-self-review.md](2026-10-13-spike-window-self-review.md) | The spike's self-review of its port; not the independent review |
| [2026-10-13-window-proof-conventions.md](2026-10-13-window-proof-conventions.md) | Conventions that make carrying proofs over mirror changes cheaper |
| [2026-10-13-charter-proof-campaign.md](2026-10-13-charter-proof-campaign.md) | The campaign charter: six WireGuard properties in dependency order |
| [2026-10-14-charter-proof-campaign-2.md](2026-10-14-charter-proof-campaign-2.md) | Charter for proof campaign 2: the handshake and configuration group (Noise state machine, index uniqueness, roaming, configuration semantics, progress, timer discipline), beside campaign 1 under a disjointness rule |
| [2026-10-14-proof-campaign-2.md](2026-10-14-proof-campaign-2.md) | Campaign 2 status, scoped proof results, findings and reproduction |
| [2026-10-16-proof-campaign-2-state-split.md](2026-10-16-proof-campaign-2-state-split.md) | Completed native-world retrofit: retyped/corrected/retained/deleted counts, claim/frame split and inherited gate lag |
| [2026-10-17-proof-campaign-2-initialized-giveup.md](2026-10-17-proof-campaign-2-initialized-giveup.md) | Accepted initialized generated retry/give-up witness: partial-exchange cleanup without observed session allocation; runtime scope and reproduction |
| [2026-10-18-proof-campaign-2-confirmation-incarnations.md](2026-10-18-proof-campaign-2-confirmation-incarnations.md) | Accepted initialized device recreation reuses a raw keypair store ID for distinct allocations: statement-artefact finding, runtime scope and reproduction |
| [2026-10-19-proof-campaign-2-supplied-pending.md](2026-10-19-proof-campaign-2-supplied-pending.md) | H5 accepted supplied-record pending identity after nested requeue; exact runtime witness, refused empty-dispatch control and mirror follow-up |
| [2026-10-20-proof-campaign-2-namespace-pin.md](2026-10-20-proof-campaign-2-namespace-pin.md) | H5 accepted namespace-pin alias leaves cleanup pending: fixture-domain review, interpreter recipe and mirror request |
| [2026-10-18-charter-proof-campaign-3.md](2026-10-18-charter-proof-campaign-3.md) | Charter for proof campaign 3: the high-consequence group (nonce safety, transmit authorization and conservation, authenticated effects and silence, handshake replay resistance, responder key confirmation, key retirement), revised against its independent review; DoS resource bounds and the routing composition deferred with the exposure named |
| [2026-10-18-proof-campaign-3.md](2026-10-18-proof-campaign-3.md) | Campaign 3 result reports: scoped T1/T2/T3/T6 claims, conditional T4/T5 claims, statement amendments, findings and validation |
| [2026-10-18-review-campaign-3-charter.md](2026-10-18-review-campaign-3-charter.md) | Historical review of campaign 3's goals and proposed contract changes; read with the revised six-result charter and final result reports |
| [2026-10-14-charter-binary-tv.md](2026-10-14-charter-binary-tv.md) | Charter for the scoping of binary-level translation validation: the mirror against the compiled oracle under Kraken's x86-64 semantics, a probe on one WireGuard function |
| [2026-10-15-charter-binary-adequacy.md](2026-10-15-charter-binary-adequacy.md) | Charter for the binary-level adequacy grind: one theorem per anchored WireGuard function under Kraken, region lemmas between correspondence points, the trust base in one file |
| [2026-10-15-binary-tv-scoping.md](2026-10-15-binary-tv-scoping.md) | Instruction census and executable three-way index-lookup probe under Kraken; blockers, state relation and checker estimates |
| [2026-10-16-plan-executable-binary-correspondence.md](2026-10-16-plan-executable-binary-correspondence.md) | Build sequence for executable reconstruction, persistent paired Kraken/mirror execution, workload debugging and proof of the same assertions; index pilot followed by the unfinished allowed-IPs loop |
| [2026-10-18-charter-paired-index-subsystem.md](2026-10-18-charter-paired-index-subsystem.md) | Next paired-execution increment: complete removal and replacement proofs, lookup under one executable reconstruction, and finite-sequence composition over a retained heap; fresh-function cost and reuse measurements |
| [2026-10-15-design-state-split.md](2026-10-15-design-state-split.md) | Design for the state split (revision 2, against Codex#4's review): per-subsystem worlds (WireGuard with routing inside, the file layer, seccomp, one shared task store, the fixture, the ambient effects), `FS.M` and `Seccomp.M` stacked on a `TaskM` layer, the within-WireGuard components over existing owners, the compile-driven retrofit with the landed campaign-1 tree as its baseline, the staging and estimate; the review dispositions |
| [2026-10-16-proof-state-split.md](2026-10-16-proof-state-split.md) | Completed campaign-1 state-split retrofit: theorem census, type-grounded deletions, full gate/replay and reconstructed runtime witnesses |
| [2026-10-16-proof-state-split-findings.md](2026-10-16-proof-state-split-findings.md) | Checked obsolete-observer differences and commands that reproduce them |
| [2026-10-17-r3-current-identity.md](2026-10-17-r3-current-identity.md) | R3 fixture, native maintenance and same-witness current peer identity at successful publication; validation and remaining initialized closure |
| [2026-10-17-r3-reached-routing.md](2026-10-17-r3-reached-routing.md) | R3 native index/creation/handshake identity and actual consumed-to-Stack routing; validation and remaining initialized joins |
| [2026-10-17-r3-current-journal.md](2026-10-17-r3-current-journal.md) | R3 native receive/lifecycle identity, actual session journal and joint routing primitives; validation and remaining initialized joins |
| [2026-10-17-r3-receive-cuts.md](2026-10-17-r3-receive-cuts.md) | R3 native receive, positional journal checks, anchored consume identity and joint allowed-IP projections; validation and remaining initialized joins |
| [2026-10-17-r3-configuration-cuts.md](2026-10-17-r3-configuration-cuts.md) | R3 concrete worker checks, receiving-owner bounds, conditional consume identity and exact configuration projections; validation and remaining initialized joins |
| [2026-10-17-r3-caller-cuts.md](2026-10-17-r3-caller-cuts.md) | R3 scheduler checks, receiving-owner receive/decrypt contracts and exact whole wgSet projections; validation and remaining initialized joins |
| [2026-10-17-r3-lifecycle-cuts.md](2026-10-17-r3-lifecycle-cuts.md) | R3 exact joint syscall/runner projections and receiving-owner poll, workers, configuration and lifecycle; validation and remaining initialized joins |
| [2026-10-17-r3-scheduler-cuts.md](2026-10-17-r3-scheduler-cuts.md) | R3 checked handshake, scheduler/deferred work and positional publication-to-consume anchors; validation and remaining caller closure |
| [2026-10-17-r3-initialized-owner.md](2026-10-17-r3-initialized-owner.md) | R3 initialized current/owner checks, packet peer frontiers and concrete completion/poll/Stack retention; validation and remaining packet/routing joins |
| [2026-10-17-r3-consume-entries.md](2026-10-17-r3-consume-entries.md) | R3 strict-prefix consume certificates, contemporaneous poll routing and packet transport through native ingress/handshake/removal and observed workers; validation and remaining initialized joins |
| [2026-10-17-r3-publication-closure.md](2026-10-17-r3-publication-closure.md) | R3 initialized publication transport, strict-prefix consume certificates and specified Stack-entry joins; validation and remaining routing/transmit closure |
| [2026-10-17-r3-initialized-authorization.md](2026-10-17-r3-initialized-authorization.md) | R3 initialized incoming authorization and actual transmit handoffs followed by Stop; validation and remaining initialized transmit join |
| [2026-10-17-r3-transmit-source.md](2026-10-17-r3-transmit-source.md) | R3 native handoff receipts, positional routing and actual caller source; validation and remaining initialized transmit join |
| [2026-10-17-r3-initialized-transmit.md](2026-10-17-r3-initialized-transmit.md) | R3 initialized outgoing authorization through every committed caller; exact RX projection, stopped prefixes, validation and coverage boundary |
| [2026-10-17-r4-stable-boundaries.md](2026-10-17-r4-stable-boundaries.md) | R4 fixture/drain/decrypt boundaries, clear-work reservations, nullable slot invariants and Stack transport; validation and remaining initialized conservation |
| [2026-10-17-r4-poll-work-conservation.md](2026-10-17-r4-poll-work-conservation.md) | R4 concrete poll/NAPI/decrypt boundaries, send/clear reservation payments and nullable key-slot transport; validation and remaining initialized conservation |
| [2026-10-17-r4-reference-accounts.md](2026-10-17-r4-reference-accounts.md) | R4 source-owned base/work/TX/cursor accounts and callback acquisition retention; validation and remaining initialized conservation |
| [2026-10-17-r4-holder-flow.md](2026-10-17-r4-holder-flow.md) | R4 complete reference accounts through admission, poll/NAPI/decrypt, work drains, dump sockets and encrypted TX completion; validation and remaining initialized conservation |
| [2026-10-17-r4-lifecycle-workers.md](2026-10-17-r4-lifecycle-workers.md) | R4 complete accounts through creation/retirement, TX/encryption, dump callers, session setup and two timers; validation and remaining initialized conservation |
| [2026-10-17-r4-auxiliary-configuration.md](2026-10-17-r4-auxiliary-configuration.md) | R4: auxiliary state and peer configuration; checkpoint scope, validation and review |
| [2026-10-17-r4-dispositions.md](2026-10-17-r4-dispositions.md) | R4: source-selected packet dispositions; checkpoint scope, validation and review |
| [2026-10-17-r4-full-ring.md](2026-10-17-r4-full-ring.md) | R4: the two carried slots and the W7 drain; checkpoint scope, validation and review |
| [2026-10-17-r4-ingress-boundary.md](2026-10-17-r4-ingress-boundary.md) | R4: device boundaries and dynamic ingress; checkpoint scope, validation and review |
| [2026-10-17-r4-ingress-coverage.md](2026-10-17-r4-ingress-coverage.md) | R4: initialized ingress coverage and saved TX work; checkpoint scope, validation and review |
| [2026-10-17-r4-initial-account.md](2026-10-17-r4-initial-account.md) | R4: initialized source accounts; checkpoint scope, validation and review |
| [2026-10-17-r4-live-frontier.md](2026-10-17-r4-live-frontier.md) | R4: initialized live encryption-ring bounds; checkpoint scope, validation and review |
| [2026-10-17-r4-outer-boundary.md](2026-10-17-r4-outer-boundary.md) | R4: outer entries and complete batch accounts; checkpoint scope, validation and review |
| [2026-10-17-r4-scheduler-lifecycle.md](2026-10-17-r4-scheduler-lifecycle.md) | R4: scheduler and lifecycle accounts; checkpoint scope, validation and review |
| [2026-10-17-r4-source-composition.md](2026-10-17-r4-source-composition.md) | R4: native receivers and source composition; checkpoint scope, validation and review |
| [2026-10-17-r4-traffic-boundary.md](2026-10-17-r4-traffic-boundary.md) | R4: complete traffic calls and lifecycle entries; checkpoint scope, validation and review |
| [2026-10-17-r4-worker-closure.md](2026-10-17-r4-worker-closure.md) | R4: observed receive and scheduler closure; checkpoint scope, validation and review |
| [2026-10-15-design-b4-load-ratelimiter.md](2026-10-15-design-b4-load-ratelimiter.md) | B4 design, revised against its review: the flood run exactly over `wg_batch` with a named checker rule change (no counter record: the instruments already carry it), the entry allocation as a kind-305 site with no kernel change, the two-table uninit fix; the ratelimiter GC deferred to its own stream with the exclusion's reason sharpened; 21 findings dispositioned |
| [2026-10-15-design-b4-review.md](2026-10-15-design-b4-review.md) | Independent review of the B4 design: 21 findings; build questions 1 and 3 with changes, redesign the GC |
| [2026-10-15-design-c-fib-trie.md](2026-10-15-design-c-fib-trie.md) | Design C: the IPv4 FIB trie as a mirror module; the fixture's tables measured from the coverage and comparison streams, the trie's shape, scope, corpus, mutants, frames, estimate |
| [2026-10-13-review-r5-counterexamples.md](2026-10-13-review-r5-counterexamples.md) | The independent review of the campaign's R5 counterexamples: three statement artefacts, design nuances at most, no tray entry |
| [2026-10-17-review-campaign-1-landing.md](2026-10-17-review-campaign-1-landing.md) | The independent review of proof campaign 1's landing (`proofs/campaign` at 6a357a90): land with named changes; gate, kernel replay and all eleven witnesses rerun; 13 findings, none blocking |
| [2026-10-18-proof-gro-carry.md](2026-10-18-proof-gro-carry.md) | Campaign 1 carried over corrected GRO classification and same-flow completion: changed order contracts, theorem counts and validation |
| [2026-10-14-campaign-2-mirror-requests.md](2026-10-14-campaign-2-mirror-requests.md) | Campaign 2 mirror requests and subsequent dispositions; historical acceptance witnesses retain their original pins |
| [2026-10-15-campaign-2-shared-frame-followup.md](2026-10-15-campaign-2-shared-frame-followup.md) | Historical request for additional shared proof-frame dependencies |
| [2026-10-15-campaign-2-shared-frame-request.md](2026-10-15-campaign-2-shared-frame-request.md) | Outer-removal frame request, closed for table safety rather than whole-driver coherence |
| [2026-10-17-proof-campaign-2-backlog-carry.md](2026-10-17-proof-campaign-2-backlog-carry.md) | Historical backlog fixture carried to a corrected refusal |
| [2026-10-17-proof-campaign-2-cookie-bound.md](2026-10-17-proof-campaign-2-cookie-bound.md) | Arbitrary-state counterexample to bounding receive-ring metadata by its count |
| [2026-10-17-proof-campaign-2-missing-clock.md](2026-10-17-proof-campaign-2-missing-clock.md) | Legacy give-up records omit a base-clock input; counterexample to the old totality domain |
| [2026-10-17-proof-campaign-2-peer-release.md](2026-10-17-proof-campaign-2-peer-release.md) | Peer-release totality needs cleanup guards for queued work and timers |
| [2026-10-17-proof-campaign-2-persistent-owner.md](2026-10-17-proof-campaign-2-persistent-owner.md) | Arbitrary-state counterexample: local hashed-owner coherence does not suffice for persistent keepalive |
| [2026-10-17-proof-campaign-2-placeholder-pending.md](2026-10-17-proof-campaign-2-placeholder-pending.md) | Historical initialized placeholder-mode pending-work witness; read with the later H5 repair |
| [2026-10-17-proof-campaign-2-queued-handshake.md](2026-10-17-proof-campaign-2-queued-handshake.md) | Statement correction after the queued-handshake record change |
| [2026-10-17-proof-campaign-2-removal-carry.md](2026-10-17-proof-campaign-2-removal-carry.md) | Peer-removal contracts restored to include the crypt-work guard |
| [2026-10-17-proof-campaign-2-session-alias.md](2026-10-17-proof-campaign-2-session-alias.md) | Arbitrary-state session-publication counterexample requiring slot and cursor freshness |
| [2026-10-17-proof-campaign-2-timer-carry.md](2026-10-17-proof-campaign-2-timer-carry.md) | Timer arming and deletion statements carried to the timer-wheel state |
| [2026-10-19-campaign-2-environment-carry.md](2026-10-19-campaign-2-environment-carry.md) | Campaign 2 carry over environment fixes, with checkpoint validation and inherited failures recorded |
| [2026-10-19-campaign-2-getter-frame-followup.md](2026-10-19-campaign-2-getter-frame-followup.md) | Getter metadata framing resolved within the owned campaign proofs |
| [2026-10-19-proof-campaign-2-prefill-blocker.md](2026-10-19-proof-campaign-2-prefill-blocker.md) | Historical Prefill specialization failure and the subsequently adopted staged bridge |
| [2026-10-19-review-campaign-3-staged-origin.md](2026-10-19-review-campaign-3-staged-origin.md) | Source review of staged provenance and the remaining transmit-binding joins |
| [2026-10-19-review-campaign-3-t2-completeness.md](2026-10-19-review-campaign-3-t2-completeness.md) | Source review of gaps in forward transmit conservation at its checkpoint |
| [2026-10-19-review-campaign-3-t2-cuts.md](2026-10-19-review-campaign-3-t2-cuts.md) | Source review of T2 conservation boundaries and coverage premises |
| [2026-10-19-review-campaign-3-t2-native-cut-closure.md](2026-10-19-review-campaign-3-t2-native-cut-closure.md) | Follow-up source review of remaining native-cut coverage for T2 |
| [2026-10-20-proof-campaign-2-prefill-investigation.md](2026-10-20-proof-campaign-2-prefill-investigation.md) | Prefill proof factoring at stock resource limits, later integrated with initialization |

## Reviews of the whole

| Document | Contents |
| --- | --- |
| [2026-10-20-fresh-eyes-scope-review.md](2026-10-20-fresh-eyes-scope-review.md) | Independent directional review of the mirror and three proof campaigns against the goal of verifying real Linux: execution-domain and statement boundaries, proof maintenance, ranked recommendations and pivot criteria |
| [2026-10-14-pre-release-review.md](2026-10-14-pre-release-review.md) | The pre-release review: 14 critiques an outside expert would make, ranked by damage and fairness, with a fix for each; the two concrete evidence defects (the foreign-function rule, the timer-input reconstruction) and the self-selected domain lead |

## Binary follow-ons

- [Index insertion charter](2026-10-18-charter-paired-index-insertion.md),
  [report](2026-10-18-paired-index-insertion.md) and
  [review](2026-10-18-review-paired-index-insertion.md): input-driven insertion
  and retained-heap composition under explicit contracts. Their original
  pending-gate status predates the combined s5 landing.
- [Callback charter](2026-10-19-charter-paired-callbacks.md),
  [report](2026-10-19-paired-callbacks.md) and
  [review](2026-10-19-review-paired-callbacks.md): bounded image callbacks and
  first-return permissions.
- [Allowed-IPs scaling charter](2026-10-20-charter-binary-allowedips.md),
  [report](2026-10-20-binary-allowedips.md) and
  [landing review](2026-10-20-review-binary-allowedips-landing.md): closed as a
  partial experiment with zero newly completed functions. Insertion remains
  open; the follow-on direction is a typed heap view.

See [binary/README.md](../binary/README.md) for the current build procedure,
artifact limitations and the distinction between local and external checks.

| Document | Contents |
| --- | --- |
| [2026-10-15-binary-adequacy.md](2026-10-15-binary-adequacy.md) | Milestone-1 lookup theorem, transport premises and chronological validation checkpoints |
| [2026-10-15-review-binary-milestone-1.md](2026-10-15-review-binary-milestone-1.md) | Independent milestone-1 trust-surface review; see the s5 landing assessment for later dispositions |
| [2026-10-16-goal-binary-proof-refactoring.md](2026-10-16-goal-binary-proof-refactoring.md) | Proof-refactoring experiment and the sequential relational sibling to milestone 1 |
| [2026-10-18-paired-index-subsystem.md](2026-10-18-paired-index-subsystem.md) | Sequential index-function and retained-heap composition report; later acceptance is recorded in the s5 assessment |
| [2026-10-18-plan-paired-call-increment.md](2026-10-18-plan-paired-call-increment.md) | Complete-call experiment, proof-cost measurements and remaining removal/capture work |
| [2026-10-18-review-paired-index-subsystem.md](2026-10-18-review-paired-index-subsystem.md) | Independent review of the sequential fixed-allocation index subsystem |
| [2026-10-19-review-paired-callback-charter.md](2026-10-19-review-paired-callback-charter.md) | Review of the callback charter and first-return permission dependencies |
| [2026-10-20-review-binary-allowedips-charter.md](2026-10-20-review-binary-allowedips-charter.md) | Review of the allowed-IPs mutation charter and its composition scope |

## Retired

[history/](history/README.md) holds superseded proposals and first-prototype
proof artifacts. The [old machine setup](history/SETUP-new-machine.md) is also
historical. These documents are not current setup instructions or project
direction.

| Document | Contents |
| --- | --- |
| [history/2026-09-19-rough-plan.md](history/2026-09-19-rough-plan.md) | Initial prototype sketch; superseded |
| [history/2026-09-20-prototype-proposal.md](history/2026-09-20-prototype-proposal.md) | First prototype proposal; superseded |
