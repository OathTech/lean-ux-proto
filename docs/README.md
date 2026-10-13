# Documents

Living documents first, then the dated ones grouped by subject. A dated
document records a design, a review or a decision as it stood on its date;
it is history, not setup instructions. Setup is
[REPRODUCING.md](../REPRODUCING.md); the standing rules are
[AGENTS.md](../AGENTS.md).

## Living documents

| Document | Contents |
| --- | --- |
| [decisions.md](decisions.md) | The register of decisions, dated, each tagged with its provenance (user or agent) |
| [upstream-tray/INDEX.md](upstream-tray/INDEX.md) | The tray of kernel findings: numbered reports on kernel behaviour that might concern its maintainers, for future analysis and filing; reports only, no patches |
| [proofs.md](proofs.md) | The proof tree's map, the register of proved results with the mirror commit each holds over, how a result is added |
| [2026-10-11-interface.md](2026-10-11-interface.md) | The shared tables: wire opcodes, record kinds, hidden-site and allocation-site ids, fixture flags, file ownership by stream |
| [worktree-practices.md](worktree-practices.md) | Worktrees, shared inputs, private outputs, cleanup |
| [offline-usage.md](offline-usage.md) | Reusing a staged environment without network access |
| [history/SETUP-new-machine.md](history/SETUP-new-machine.md) | Retired on 2026-10-13: the October 2026 machine migration notes, kept for their checklist; the commands and counts in it are of that date |
| [nono-profile-proposal.md](nono-profile-proposal.md) | The sandbox profile the project's devboxes run under; devbox-specific |

## Plans and strategy

| Document | Contents |
| --- | --- |
| [2026-09-29-way-forward.md](2026-09-29-way-forward.md) | The assessment that set the thin-layer direction: a behavioural mirror, no theorem proving, data and control-flow correspondence |
| [2026-09-29-next-plan.md](2026-09-29-next-plan.md) | Finish the FD/eventfd slice, then WireGuard |
| [2026-10-03-choice-stream-strategy.md](2026-10-03-choice-stream-strategy.md) | Hidden inputs recorded at generic kernel interception points and replayed: the choice stream |
| [2026-10-03-hidden-inputs-design.md](2026-10-03-hidden-inputs-design.md) | The hidden-input record kinds and their sites |
| [2026-10-03-steering-design.md](2026-10-03-steering-design.md) | Steering a hidden input to a chosen outcome; the kernel mechanism later superseded |
| [2026-10-06-contended-host.md](2026-10-06-contended-host.md) | Check failures on a contended host, and the rule that a scheduling-dependent failure is a modelling gap, never a retry |
| [2026-10-06-future-proof-paths.md](2026-10-06-future-proof-paths.md) | Cheap conventions that keep later proof work possible without doing it |
| [2026-10-08-pause-state.md](2026-10-08-pause-state.md) | What was on main and on branches at the October pause; historical |
| [2026-10-11-dispatch-order.md](2026-10-11-dispatch-order.md) | Recording which queued work unit a section runs, at the source |
| [2026-10-12-kernel-scout.md](2026-10-12-kernel-scout.md) | Candidate next mirror targets scored; epoll and seccomp chosen |
| [2026-10-12-simulation-target-review.md](2026-10-12-simulation-target-review.md) | Whether the mirror is a suitable target for a later simulation proof: suitable with named representation changes, since landed |

## WireGuard

| Document | Contents |
| --- | --- |
| [2026-09-30-wireguard-stage-a-report.md](2026-09-30-wireguard-stage-a-report.md) | Stage A report: configuration and device state |
| [2026-09-30-wireguard-stage-b1-report.md](2026-09-30-wireguard-stage-b1-report.md) | Stage B1 report: transmit and routing |
| [2026-10-01-wireguard-stage-b2-report.md](2026-10-01-wireguard-stage-b2-report.md) | Stage B2 report: the receive path up to Noise |
| [2026-10-01-wireguard-stage-c-report.md](2026-10-01-wireguard-stage-c-report.md) | Stage C report: the Noise responder |
| [2026-10-04-d1-sprint.md](2026-10-04-d1-sprint.md) | D1: the initiator role, in parallel streams |
| [2026-10-04-d2-data-plane.md](2026-10-04-d2-data-plane.md) | D2 design: the data plane, workers and queues |
| [2026-10-04-d2-sprint.md](2026-10-04-d2-sprint.md) | D2 sprint record |
| [2026-10-05-d3-timers.md](2026-10-05-d3-timers.md) | D3: timers, timer sections and virtual time |
| [2026-10-05-a-alloc.md](2026-10-05-a-alloc.md) | A: allocation outcomes recorded and steered |
| [2026-10-05-e-dos.md](2026-10-05-e-dos.md) | E: cookies and the rate limiter under load |
| [2026-10-05-e-probe-results.md](2026-10-05-e-probe-results.md) | E: the under-load reachability probe |
| [2026-10-05-l-lifecycle.md](2026-10-05-l-lifecycle.md) | L: device lifecycle |
| [2026-10-06-wireguard-census.md](2026-10-06-wireguard-census.md) | Coverage census of WireGuard's source against the mirror; the W rows |
| [2026-10-06-w1-w2-netlink.md](2026-10-06-w1-w2-netlink.md) | W1 and W2: netlink completeness and multi-message dumps |
| [2026-10-06-w3-w12.md](2026-10-06-w3-w12.md) | W3 and W12: two small coverage workstreams |
| [2026-10-06-w4-w7-transmit-bulk.md](2026-10-06-w4-w7-transmit-bulk.md) | W4 and W7: transmit shapes and bulk queues; the full-ring tier and the open two-drop finding |
| [2026-10-06-w5-w6-receive.md](2026-10-06-w5-w6-receive.md) | W5 and W6: receive shapes and the stack's reactions to inner packets |
| [2026-10-06-w8-w9-netns-routing.md](2026-10-06-w8-w9-netns-routing.md) | W8 and W9: netns exit, socket errors and routing |
| [2026-10-13-w7-full-ring-tier.md](2026-10-13-w7-full-ring-tier.md) | The W7 full-ring tier: the two silent drops at the 1024-item wrap explained from the records (two uncleared carried slots, no interleave), the tier's five traces |
| [2026-10-13-review-items-7-8.md](2026-10-13-review-items-7-8.md) | Review items 7 and 8: the runner's budgets as derived or record-driven measures with the kind-310 end-of-wait read, and jiffies as the C's 64-bit type with its comparisons declared |

## Pipes, epoll and seccomp

| Document | Contents |
| --- | --- |
| [2026-09-29-fd-eventfd-slice-report.md](2026-09-29-fd-eventfd-slice-report.md) | The file-descriptor and eventfd slice, final report |
| [2026-10-05-pipes-reconnaissance.md](2026-10-05-pipes-reconnaissance.md) | Pipes as the scale test, reconnaissance |
| [2026-10-05-p-pipes.md](2026-10-05-p-pipes.md) | P: pipes stage 1 design, including the signal decision P9 |
| [2026-10-12-epoll-design.md](2026-10-12-epoll-design.md) | Epoll over the FS slice: design v2 with its independent audit and audit response; landed 2026-10-13 |
| [2026-10-12-seccomp-design.md](2026-10-12-seccomp-design.md) | Seccomp as a single-task mirror with the eBPF engine as a service: design v2 with its independent audit, audit response and the user's config case (approved 2026-10-13) |

## Proofs

| Document | Contents |
| --- | --- |
| [2026-10-12-charter-window-proof.md](2026-10-12-charter-window-proof.md) | The first proof charter: replay freedom of the receive counter window, Rule Zero, the layered models |
| [2026-10-12-spike-window-review.md](2026-10-12-spike-window-review.md) | The independent review of the spike, in two parts: the original and its carry-over onto the new mirror |
| [2026-10-13-spike-window.md](2026-10-13-spike-window.md) | The spike's own report |
| [2026-10-13-spike-window-self-review.md](2026-10-13-spike-window-self-review.md) | The spike's self-review of its port; not the independent review |
| [2026-10-13-window-proof-conventions.md](2026-10-13-window-proof-conventions.md) | Conventions that make carrying proofs over mirror changes cheaper |
| [2026-10-13-charter-proof-campaign.md](2026-10-13-charter-proof-campaign.md) | The campaign charter: six WireGuard properties in dependency order |

## Retired

[history/](history/README.md) holds the superseded proposals and the proof
artefacts of the first prototype. They are not current direction and do not
authorise recreating what they describe.
