# Campaign 2 carry over the environment fixes

## Current status

The request is fulfilled by main 3308c49a, merged into campaign 2 at
a9845661. The five inherited source failures are repaired. Campaign 2 has
removed its two temporary deletion variants and carried its dependents.
The corrected full gate passes 3,119 jobs and 1,761 terminal statements
with standard axioms only; fresh whole-tree kernel replay exits zero, and
all 12 counterexample recipes pass. The report records the two failed
owned-carry builds that preceded the corrected pass. All six register rows
are current for their checked claims over 3308c49a.
The later [Prefill investigation](2026-10-20-proof-campaign-2-prefill-investigation.md)
checks the exact source equation with a staged proof at stock limits. That
prototype awaits integration; H5 global termination is still unproved. No
further mirror or shared-layer change is requested.

The remainder of this document records the earlier failed carry attempts
and the scoped work completed while the shared repair was pending.

## Historical request and carry


Main `3f3879e0` is merged into `proofs/campaign-2`. The preceding checkpoint
`46b6089c` passed 3,054 build jobs, all 1,690 terminal axiom checks and fresh
whole-tree kernel replay over `783510e8`. These results do not establish a
pass over the changed mirror. All six register rows remain lagging while the
carry is incomplete.

## Shared-layer request

Campaign 1 owns the following source observers and their erasure/frame
families. They need to follow the newly landed source before campaign 2's
whole-driver claims can be checked. The first post-merge scoped build fails in `Logged/Scheduler.lean`,
`WG/NetlinkDump/DeviceSource.lean`, `WG/Lifetimes/BatchActivation.lean` and
`WG/Queues/RxDrainBoundary.lean`.
The remaining entries below are source/dependency inspection, not a claim
that the build has independently reached every listed file.

| Shared family under `Leanux/Proofs/` | Required carry | Campaign 2 dependents |
| --- | --- | --- |
| `WG/Queues/SchedulerSource`, `SourceScheduler`, `RxActivationRunHistory`; `WG/Lifetimes/BatchActivation` | Capture the actual refills read and use occupancy plus refills plus one, including the changed exhaustion message | Finite activation, driver tags, initialized committed receipts |
| Those scheduler dispatch/selection factors, `WG/Queues/RxScheduleHistory`, `WG/Lifetimes/BatchScheduler`, `Logged/Scheduler` | Pending-aware device dispatch and placeholder selection | All whole-driver scheduler compositions |
| `WG/Lifetimes/EnvWorkersAudit.requireDrainedPrefix`, `WG/Queues/RxDrainBoundary` | Insert the pending-device-unit rejection between queue and NAPI checks, preserving the exact error | Deferred, traffic and batch completion |
| `WG/Lifetimes/RunnerAudit`, `WG/Queues/RxRunnerHistory`, `JointRunnerSource`, `RunnerOperation` | Insert the supplied-mode pending guard between suspended-work and NET_RX checks | Initialized Noise, Index, Roaming, timer hooks and progress receipts |
| `WG/NetlinkDump/DeviceSource`, `WG/Lifetimes/DumpAccess`, `WG/Queues/DumpReservation` | Transport the snapshot taken before peer-nest reservation through the tail and cancellation | Configuration readback and whole-driver dump contracts |
| Concrete shared proofs unfolding `AmbientM.hidden` | Account for section-start pending clearing before the supplied/placeholder split | Record and ambient frames |

The old source observers have different behavior, so an adapter proving a
frame alone cannot restore their erasure equalities. Local variants would
copy multiple scheduler, runner and dump layers, beyond the permitted few
shared lemmas. Campaign 2 therefore requests the campaign-1 carry, keeps
those shared files unchanged, and continues the independent owned repairs.
No mirror change is requested: the three environment defects are fixed.

## Owned carry and scope

The independent carry starts with the native Runner boundary source/audit,
activation exit accounting, record-suffix proof, pending-aware dispatch,
and the native empty-dump regression. Activation observations must retain
both occupancy and refills and their actual read cuts. Merely changing the
arithmetic bound does not prove that the budget funds every possible item.

The accepted Runner boundary now implies that a supplied-mode boundary has
no pending identities. The wait guard rejects known worker indices in every
mode; raw-list emptiness there additionally needs a known-index invariant.
The Runner guard alone does not establish placeholder-mode emptiness.

The historical refill and pending witnesses must change their expected
outcomes: the occupancy-only failure disappears, the missing redispatch is
rejected, and the supplied empty redispatch is accepted. Their historical
reports remain evidence about the earlier mirror. Current observer receipt
checks will be restored only after their source observers are carried.

Validation command for the initial carry inventory:

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Progress.Statements Leanux.Proofs.WG.Config.Statements
```

This run fails; it is not a gate pass. Per-file repairs and final validation
will be recorded here as they close. No frame is deleted on compile failure,
and no shared proof or mirror file is edited.

The first independent owned repair build passes 147 jobs, followed by
94-job observation and 80-job native-regression builds. Shared source
observers remain unchanged; their blocked whole-run claims remain lagging.

The first full gate after the native carry also fails in
`Logged/Checkpoints.executeTraceCheckpoints_erases`: its runner observation
must include the new completion guard. The same run identifies two further
owned dump factors (`Config/MultiPeerDumpSource`, `Config/SocketReadbackSource`),
which campaign 2 is carrying. This is a failed gate; its axiom stage is skipped.
The token/import checks pass. The owned dependent activation/decrypt/receive
and cookie build passes 260 jobs; the corrected dump headlines pass a 108-job
build. A scoped root audits ten exact headlines and 149 support declarations
with standard axioms only. Fresh scoped replay passes at actual exit zero.

The first two owned dump blockers now build (111 jobs). The corrected cursor
source and model also build alongside the new finite FS callers (154 jobs),
including empty-list and dead-cursor cancellation from the pre-header
snapshot. A 72-declaration scoped audit and fresh replay pass. Outer peer
and mixed-page pagination are still being carried; none of the shared
observer failures has been hidden or repaired in campaign 2.

The outer peer/mixed pagination carry now passes a 207-job build. The native
empty-device callback restores the reservation; the mixed raw-plan count
remains a proved sufficient bound. A combined pagination/epoll root audits
66 declarations including four exact terminal bodies with standard axioms
only; fresh replay exits zero. The next full gate fails only in the five
shared modules listed above (3,078 planned jobs), with no further owned
failure. Dependent owned modules skipped behind those failures remain
unvalidated; the terminal axiom stage is skipped. Token/import checks pass.
This shared carry is still required; local substitutes would copy layers.

## Owned factor route, 2026-10-19

The private-key stage and maintenance finite proofs now avoid the blocked
high-level observers by moving already-owned native factors into five small
files. The retained shared JointRemoval/JointDestruct dependencies build
unchanged. No shared variant or layer is copied. Existing owned key wrappers
are generalized once, with original theorem headers preserved.

The subsequent full gate has 3,096 planned jobs and still fails in exactly
the five shared modules listed above. It reports no owned failure; dependent
modules skipped behind those failures remain unvalidated. The axiom phase
does not run after the build failure. The 444-job maintenance/key and
183-job installation/key-client scoped builds pass, with 85 standard-axiom
audits and fresh KeyInstallReplay at exit zero. Complete native activation/scheduler evaluation now passes through the
carried owned sources: 303 scoped jobs, 47 standard-axiom audits and fresh
ActivationCarryReplay. This preserves five existing claims but leaves the
shared-enum observer wrapper dependencies lagging.

## Concrete caller boundary, 2026-10-19

The owned route now checks complete mixed peer/device configuration,
open/up, native send/crypt/drain and namespace-holder close. Peer creation's
CoreSource extraction recovers four existing public claims without the
BaseCreation observer closure. The two old BaseCreation-facing factors and
the shared-enum/placeholder deferred wrappers remain retained and lagging.
The new aggregate gate has 3,109 planned jobs and fails only in the same
five shared modules, with no reported owned failure.

Traffic needs existing Lifetimes.TrafficSource factories injectWith,
afterBatchWith, floodWith and batchWith, plus Lifetimes.batchItemWith.
TrafficSource imports RxTrafficAppends, whose syscall/dump observer chain
reaches NetlinkDump.DeviceSource. BatchItemSource imports RxEnvBatchHistory,
whose worker/scheduler chain reaches Lifetimes.BatchActivation. The owned
Noise/DriverTagTrafficSource and Progress/CommittedTrafficSource merely
instantiate these same factories; moving the owned erasure tactic cannot
remove the dependencies. Both architectures were inspected. Copying all
five factories and their erasure layer would exceed a few local variants,
so no such copy is made. The existing shared carry, or a campaign-1 light
source extraction, unblocks the held concrete instance.

## Native outer callers and remaining shared boundary, 2026-10-19

Environment down/delete and the complete native timer/placeholder,
after-transmit, idle and after-advance callers now pass scoped builds
(397 and 367 jobs). Observation also closes using the existing light shared
source factor (365 jobs); 45 standard-axiom audits cover this tranche. Two explicitly named local
deletion variants stand in for the single shared factory and its source
factor; no observer layer is copied. Four owned callback seams preserve all
legacy theorem headers. The latest full gate has 3,117 planned jobs and
fails only in the same five shared modules; skipped dependents and the
shared-enum aggregate remain unvalidated. Fresh EnvironmentOuterReplay and
ObservationNativeReplay both exit zero.

The traffic dependency boundary remains exactly the two routes above.
The remaining native callbacks must compose through syscall dispatch,
taskWorkRun and executeTrace. A source audit found no additional
nonstructural primitive beyond the seven sites already supplied with finite
replacements. The closed-program Prefill specialization remains a separate
proof-form blocker, not a mirror request or a semantic counterexample.

The gate also reports the existing Env.lean String.mk deprecation and the
RxDrainBoundary unused-simp warning. They remain in the mirror/shared lane,
with no suppression or unauthorized edit in this campaign.
