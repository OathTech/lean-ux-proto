# WireGuard proof campaign

## Progress

Work is on `.worktrees/proofs-campaign`, branch `proofs/campaign`, under
[the charter](2026-10-13-charter-proof-campaign.md). The mirror remains byte-identical
to `43c7549`; coordinated validation of the syscall extension passes.
The [proof register](proofs.md#results) holds current declarations and
pins; its [model map](proofs.md#layers) supplies the complete module inventory.
Current components are not completion of the open charter properties. This campaign
has made no main integration, push, differential check or guest run.
[AGENT 2026-10-14] Keep the module inventory/register in the proof map; this report
retains current architecture, findings, reproduction provenance, effort and limits.

| Result | Current disposition |
| --- | --- |
| R1 | Uniqueness and the intentional inclusive-floor correction are proved, with pure and accepted-run witnesses. |
| R2 | Endpoint identity and failure-retaining access contracts cover the listed families, concrete Batch scheduling and isolated trials. All seven original dump calls have exact typed erasure and concrete allocation-safe failed prefixes. The audit scheduler now derives allocation validity at each recorded consistency-filter entry, including failed histories, and links those entries to safe copied trials. Fifteen original deferred-worker/guard/timer calls now carry that audit contract through dispatch, idle and advance, preserving demanded saved-map access order. Fifteen further control/observation/ingress/batch calls now retain AuditInv through actual multicast/inline scans, both flood modes and namespace cleanup. All typed dispatcher/syscall constructors now compose those calls through exact descriptor wrappers and postworker tails. Initialized whole-run allocation-identity access closure remains open through Runner; raw-reference affiliation/credit is a separate stronger property. |
| R3 | Initialized finite normal call histories refine flat-prefix updates and reached-root lookup, including full normal clear. Completed setAllowedip/removal events now cover the entire acquired-peer update, with concrete send/flush/cleanup frames and separately derived lookup/create residency. Public setPeerCmd preflight composition, enclosing configuration/Runner closure and packet paths remain open. |
| R4 | Physical rings, finite/source journals, per-poll provenance and selected GRO order, and concrete RX scheduling are checked. Accepted input refutes chronological post-GRO order. Joint pipeline conservation remains open. |
| R5 | The unconditional age/post-zero and wire-nonce readings are false in accepted mirror inputs. Rule Zero resolution retains thirteen positive local contracts, without universal replacement transport claims. |
| R6 | Cookie exclusion is proved at its original call boundary. A 19-retry/20-initiation episode refutes literal MAX=18; no universal corrected retry bound is claimed. |

**Validation status.** The syscall extension has 417 terminal declarations
(415 theorems and two definitions), including 205 R2 theorems. Wrapper/compatibility,
dispatch, enclosing syscall and terminal targets pass 228/239/240/277 jobs; the
full proof target passes 420 jobs. The capped exact eight-file scope/census/
signature/whitespace/mirror check passes, retaining all ten compatibility
signatures and 202 prior R2 terminals. Independent frozen review is clear; its
two documentation findings are corrected. A separate lower/Env/syscall source
coverage audit found no issue in its inspected surfaces. Sequential coordinated
validation passes the 420-job proof gate with all 417 declarations on permitted
axioms, fresh stock kernel replay, the 60-job default build and 124 unit tests
(22.751 seconds, one skip). The capped scope/census/whitespace check confirms all
six frozen Lean hashes. Its first run failed only because a non-trust assertion
pinned the moving shared main head; checking ancestry instead passes. The mirror remains byte-identical
to `43c7549`; no reproduction recipe or runtime behavior changes. Initialized
whole-run R2 and remaining R3/R4 closures stay open.

```sh
capped -- scripts/in-bundle scripts/proof-gate
capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
capped -- scripts/in-bundle lake build
capped -- scripts/in-bundle lake build leanux-model
capped -- scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation evaluator.test_model_replay harness.test_trace harness.test_wg harness.test_linux
```

**Shared reproduction provenance.** Eleven checks comprise nine accepted mirror
runs with original/observer output agreement and two expected R2 pending-dump
rejections. Generated streams establish mirror behavior, not a new Linux capture
or kernel schedule reachability. Exact recipes/commands remain with each result.
[AGENT 2026-10-14] Reconstruct the common seed from tracked `rx_roam_v6` operations
and the 40 historical hidden records formerly in `CONTENDED_ROAM_CMP`; the generator
documents provenance and transformations. The seed and ten generated JSON values
matched their pre-carry versions. This was reproduction repair, not new evidence.
[AGENT 2026-10-14] Preserve both historical R2 recipes and test their current
rejection plus accepted pre-delete boundary. Generate coherent R5/R6 caller-jiffies
records from the chosen recipe clock in source order, with independent arm-expiry
checks. W7 instead reconstructs caller values from captured arm expiry/delay using
`with_timer_caller_jiffies`; that caller clock was not independently captured.

**Carry architecture and effort.** Shared frames retain the seven-field WG view,
seccomp/prefill success and error paths, exact signed clocks/comparison operands,
record/occupancy bounds and kind-310/311 order. Current observers retain both
crypt-ahead sites, `floodExact`, both ratelimiter tables and the no-op
`requireNotPending`; they do not invent its retired getter. These are source
correspondence obligations, not additional R4/R5 property conclusions.

[AGENT 2026-10-14] Carry `43c7549` through shared full-Kernel frames for
`noteNetRxStart` and `iputReport`, projecting into the existing WG views and
retaining existing source-body proofs for pipefs and epoll. Both worker observers
now assign the already-incremented NET_RX count to the current section; record
consumption itself retains the source's ordinal update order. Filesystem and
socket callers retain the new inode-report decisions in original call order.
The timer observer carries the exact revised stall Stop text. Eight Lean files
change; terminal statements, premises and reproduction recipes are unchanged.

| Carry | Measured effort |
| --- | --- |
| Seccomp/shared frames | 17 compile passes; 36m34s. |
| Prerequisites `2c7a076` | About 40m, 12 local builds; earlier transmit/stack work five attempts. |
| Audit `f45bde8` | 14 root, six R2 and sixteen R4 build/probe calls before passing gates and nine replays. |
| Scheduler `7a92672` | 15 calls: 14 passes, one failure; 16m20s validation, 17m22s token ownership. |
| `c047e64` | 23 calls: 14 passes, nine ordinary failures (seven proofs, two replay parsers); 29m33s. |
| `43c7549` | Two capped builds, both PASS (148-job scoped closure, 321.28s; 401-job full proof closure, 298.03s); zero ordinary failures, cap kills or interruptions. All exits collected; one cheap uncapped scope/census check passed; the coordinator repeated it under capped, passing exact ten-file scope, eight frozen Lean hashes, 403 declarations, whitespace and mirror equality. 12m50s from grant 16:47:30 through full-result collection 17:00:20 UTC. Eight Lean files; independent frozen source/documentation review is clear after the status-wording correction, and sequential coordinated proof gate, fresh kernel replay, default/executable builds, 124 unit tests and eleven reproductions pass. Token returned at 17:03:32 (16m02s ownership). Recipes are unchanged. |

Carry review corrected missing caller-read success before jitter failure, obsolete
pending-worker wording, a reply-invariant copy and an accidentally lifted
`idleTimers` call that hid validator observations. Committed acceptance history
is retained; exact Stop erasure alone does not retain a failed history. These
corrections did not restrict arm-record mode. One carry repeated a known failing
goal before its diagnostic was noticed. An interrupted prerequisite worker had an
unavailable handle; its log showed a normal proof failure, and dirty worktrees were
preserved before resumption. Subsequent collected gates passed. Carried whitespace
in upstream text/patch files was outside the campaign repair diff.

## R1 — anti-replay uniqueness and the inclusive floor

**Decision [AGENT 2026-10-13].** Reuse the pure counter window, exact S2
refinement, finite mirror-call refinement and committed runner observer. Put
new arithmetic in `WG/CounterWindow`, with terminals in `WG/AntiReplay`.

**Original and proved wording.** The charter excludes counters at or below
highest seen minus 8128. The proof excludes counters strictly below it;
unseen equality may be accepted. The mirror's strict `ctrTooOld` comparison,
Linux `receive.c:counter_validate` and `selftest/counter.c` agree. This is an
intentional inclusive edge, not a mirror/kernel disagreement. The arithmetic
uses the one-based stored high-water mark, avoiding subtraction at an empty window.

**Architecture/refinement.** `CounterWindow/Bounds` proves the guard and bitmap
bounds; `mirrorCalls_refines` identifies finite original calls with pure
acceptance and final state. `Keypairs/Evolution/Bounds` adds `FloorHistory`:
an earlier accepted nonce is at most 8128 above a later one in the same
allocation lifetime. `Evolution.floor` transports it through lifecycle and
validator transitions. `runner_floor` and `runner_uniqueness` discharge the
original syscall contracts for every successful execution, including accepted
record schedules and slot reuse. No new observer or production history was
added; committed calls and discarded probes retain ReplayWindow's reviewed scope.

**Rule Zero witness.** The pure run `[8129, 1, 0, 1]` accepts `[8129, 1]`,
proved by kernel reduction. Separately, a six-operation accepted runner trace
establishes a session and accepts authenticated keepalive counters 8200 and 72
in lifetime 1: `72 = 8200 - 8128`. Original and logged JSON agree. Its explicit
records use `historical_session_seed`: tracked `rx_roam_v6` operations and the
40 historical record words documented in the generator, with datagrams from
`rx_window.json`, widened legacy section identities, adjusted second-data
clocks and synthetic site-128 end-of-wait bounds for the current timer interface.
This is an accepted non-placeholder mirror replay, not a fresh Linux capture.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r1-inclusive-floor |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/Logged/Replay.lean
```

**Effort/review.** About fifteen minutes and five local compile passes; replay
under one second. An initial dependency scan preceded the new root import and
failed; a fresh build resolved it. Two independent read-only review passes
found no correctness defect. Their reporting corrections distinguish the pure
and runner counters and reconstructed records from a new capture. Current
validation is above; no remaining R1 obligation is recorded.

**Ranked recommendations.** None: the existing validator, replay projection
and proof-side lifetime evolution suffice. A proof-driven comparison change
or production history field would not preserve altitude and is not proposed.

## R2 — lifetime identity and retained references (in progress)

**Original versus proved.** The charter requires safety of every internal access
after release across every run. Checked components establish endpoint identity
evolution and local failure-retaining access safety; initialized whole-run
composition remains open. Raw-reference affiliation and credit accounting are
separate stronger properties. The historical findings below
retarget a replacement identity, rather than resurrecting a released identity.

**Architecture/refinement.** [Terminal contracts](../Leanux/Proofs/WG/LifetimeSafety/Statements.lean)
retain exact original result, successful World and Stop; safety has its stated
invariant/callback premises. An unchanged endpoint alone does not prove access-free
execution; lifted helper coverage is separately checked against source.

| Model | Abstraction and refinement boundary |
| --- | --- |
| `Lifetimes/Store`, `Actions`, `Keypairs/Identity` | Slot/allocation stamps and original-execution transitions; `keypair_syscall_no_resurrection` and peer/packet sequence contracts. Packet primitive results are within one device epoch. |
| `Logged/Prefix`, `Focus`, `LifetimeEvent.Safe` | Mixed access/release histories outside the exception layer; packet stamps are `(ifindex, id + 1)`. All-input erasure and safe reached prefixes. A failed getter resolves no object and emits no access. |
| `ReleaseInv`, `AllocationInv` | Resident uniqueness, current slot/lifetime frontiers and past packet-epoch bounds; `allocation_initial_fixture` and concrete preservation establish allocator vacancy. Arbitrary occupied-slot behavior remains in erasure, not in a safety conclusion. |
| Ambient contracts and canonical Kernel projections | Preserve chosen invariants through source-shaped leaves; legacy interfaces project shared frames. Queue scalar preservation does not establish reference credits. |
| `SavedPeers`, prefix loops/workers | Observe demanded captured entries, including predicate misses, with saved-stamp residency obligations; exact bounded-loop erasure retains callback/exhaustion Stops. |
| `BatchTrials`, `BatchCalls` | `scheduler_family_access_erasure`, `scheduler_family_allocation_access` and `scheduler_trial_filter_access` separate committed calls from copied-World trials. The ordered filter propagates its first non-hidden Stop; each reached trial has an isolated safe prefix from the same entry invariant. |
| `Audit`, `BatchAudit` | [AGENT 2026-10-14] Carry saved consistency-filter entry facts in `AuditM` through remaining callers, avoiding separate reachability threading while retaining failed histories and separate trials. The sum event stream projects to committed lifetime events and records the actual current World/projected history immediately before each original filter, including empty filters and Stops. `AuditInv` combines current `AllocationInv` with validity of every saved entry. Result-dependent focus preserves cached predicates and old probe facts. Literal scheduler/nested-reschedule/receive-worker observers have unconditional source erasure, allocation-conditional committed projection and concrete failed-prefix safety. Empty-history local allocation validity derives safe trials at every recorded entry; exact filter correspondence preserves order and early failure without asserting unevaluated candidates ran. The literal source placement and exact filter-entry equation supply coverage; projection alone does not. |
| Deferred environment workers and timers | [AGENT 2026-10-14] Reuse Audit composition for actual scheduling and focused local lifetime calls; share captured-map optional lookups so each present peer-list occurrence emits its saved-identity read and missing entries emit none. Complete scans precede callback effects; original short circuits, section records, timer detachment, finite bounds and failures remain exact. Full-Kernel bookkeeping frames project legacy APIs, and literal timer source cuts share the original pure scan/fold. Fifteen typed calls have unconditional erasure, concrete AuditInv prefix safety and reached-trial facts from local allocation-valid entries; initialized Runner closure remains open. |
| Remaining environment callers | [AGENT 2026-10-14] Share source-only observation and per-item batch cuts, while keeping concrete Audit observers at actual device, receive, multicast and inline-poll calls. Full-Kernel leaves and an MTU/inet scalar mask retain residents/frontiers; flood queue updates preserve identity and metadata while allowing byte/source queue changes. Both flood modes keep audit-aware nested receive callbacks; complete saved-map scans, partial CQEs, delete guards, finite budgets and failed histories remain exact. Fifteen typed calls have unconditional erasure and concrete local AuditInv/reached-trial contracts; initialized Runner composition remains open. |
| Complete syscall callers | Literal callback-parametric socket/netlink/rtnetlink observers preserve source cleanup only on ordinary returns, including negative results. Shared full-WG framing covers the four holder closes/taskWorkRun; actual namespace cleanup remains in the postworker suffix. All 34 typed constructors/35 dispatch arms retain exact descriptor/route/MTU/dump guards, observation-before-fdcheck, source resets and seccomp/postworker order. Three grouped contracts give unconditional erasure, concrete AuditInv failed-prefix preservation and reached-trial facts from local entry AllocationInv. Arbitrary typed arguments need no parser-validity premise; initialized Runner composition remains open. |
| `PeerRemoval` | [AGENT 2026-10-14] Reuse fixed send/clear `runWorkerPrefix` wrappers and scalar queue/count frames to compose all seven original flush/removal calls. Exact erasure retains the 4096 drain, dispatch/placeholder order, early returns and saved-ID loops; concrete allocation safety adds no ownership or progress premise. |
| `DeviceControls` | [AGENT 2026-10-14] Compose eight original socket/device controls using a full-Kernel mask of only socket labels/incoming port and legacy frame projections. Separate source inspection justifies access-free socket lifts; saved-ID loops retain actual peer accesses, negative-return cleanup and Stop prefixes. Concrete allocation safety needs no list-validity, progress or credit assumption. |
| `DeviceCreation`/`DeviceRetirement`/`DeviceLifecycle` | [AGENT 2026-10-14] Observe guarded creation as one resident-access-free action and prove its normal allocation endpoint, avoiding an invariant at provisional epoch 0. At the original final `wg := none`, append logical releases from every actual pre-drop resident map, with packet stamps `(ifindex, id + 1)`; this accounts for store retirement, not per-object kernel frees or reference credits. Compose complete destruction/deletion with exact socket/peer-removal prefixes and queue-guard Stops. |
| Insertion and peer configuration | [AGENT 2026-10-14] Give insertion a separate node-allocation mask permitting `nextNode` changes while retaining full tracked residents/frontiers and the stricter removal frame. Share literal peer-configuration source stages below lifetime/routing imports; compose complete add/insert, setPort/setAllowedip/setPeerCmd with saved-peer writes, ordinary-negative cleanup and safe failed prefixes, without routing or attribute-validity premises. |
| Device configuration | [AGENT 2026-10-14] Share literal device-configuration continuations below the proof layers; use a full-Kernel mask for only identity/cookie-key/generation/fwmark updates and focus the existing precomputation observer. Extend the existing configuration family to complete wgSetDevice, preserving saved-ID loops, generation-before-error, put-before-remove and ordinary-return zero-key cleanup; concrete allocation safety needs no routing, attribute-validity or reference-credit assumption. |
| Local filesystem frame migration | [AGENT 2026-10-14] Prove original Wait/Pipe/PipeRead operations once over the complete WG kernel view and project the legacy contracts, retaining weak wait-IH signatures, exact source aliases and pipe geometry/progress. Source inspection separately justifies six access-free lifts; normal frames transport AllocationInv, while exact lifts retain all incoming history and original Stops. This avoids duplicate operational proofs and does not claim whole-FS or outer-run closure. |
| Complete filesystem frames and calls | [AGENT 2026-10-14] Move FSBase/Eventpoll/FS/EventpollCalls operational proofs into canonical full-WG frames and derive all 347 legacy signatures by projection. Generic SameView list/search rules retain weak callback premises; fixed-source epoll fuel results retain weak-IH APIs. Eleven typed original FS dispatch arms and actual taskWorkRun have source-audited exact unchanged-history lifts and concrete AllocationInv transport. Normal frames and exact Stop/history behavior are separate; queueing namespace cleanup does not execute it. |
| Netlink dump family | [AGENT 2026-10-14] Share literal serialization/header cuts and canonical complete-Kernel frames; mask only the two netlink socket records and project legacy APIs. Observe all seven original dump calls at demanded peer/cursor/refcount accesses, preserving new-acquire-before-old-put, queue-before-done and pop-before-next-dump. Concrete allocation safety retains failed prefixes without cursor affiliation, valid lists or drain-success premises. |

[AGENT 2026-10-13] Separate identity from saved-reference ownership, share frontier
algebra and the WG projection, and retain history outside exceptions. Observe saved
entries on demand without inserting getters. Use exact IPv4 source tails retaining
the entry route, explicit socket/rescheduling contracts and local handshake
boundaries; project canonical record/jitter/checksum/crypto/index frames. Factor
buffer allocation from its original send suffix, distinguishing refusal from Stop.
[AGENT 2026-10-14] Mask only cookie secret/birthdate and both rate tables for cookie
frames, retaining complete residents/frontiers; compose receive through exact load
factors and bounded workers, separating byte queues from resident skb stores.
Keep copied trials outside committed history. Share the node/root/sequence mask and
exact removal suffix for allowed-IP access, retaining `nextNode` and all residents;
interleave every demanded saved-map read with its hit write. Reuse concrete
index/release/staging/queue contracts for maintenance and project the legacy index
frame from one full-Kernel mask.

[AGENT 2026-10-14] R2 closes with initialized whole-run allocation-identity
access safety, including saved-object writes, demanded map reads and actual final
resident retirement. Raw-reference affiliation/credit accounting is a stronger
separate property, required where later R3/R4 arguments depend on it. This boundary
preserves every source-coverage obligation and does not claim current completion.

**Covered original families.** The map lists every module; grouped contracts cover
allocation/reference/lookup, receive enqueue/decrypt/completion/poll/stack, TX
staging/encryption/completion/workers, both socket families and loopback, five Noise
constructor/consumer/MAC calls, six handshake-send calls, four cookie calls,
handshake receive/bounded workers/UDP ingress, concrete Batch scheduling, six
allowed-IP list/removal calls, and now four key-maintenance calls plus all five
expired timer callbacks and their dispatcher, plus both flushed workers, the workqueue
drain, timer stop and after-dead/optional/all-peer removal; socket free/reinit/init,
device open/up/stop/down and namespace pre-exit; guarded creation, destruction
and deletion with actual residual-store retirement; complete allowed-IP add/insert
and setPort/setAllowedip/setPeerCmd. Concrete `AllocationInv` discharges
these local ambient contracts; source Stops and ordinary negative returns differ.
Batch callbacks are discharged, without implying R4 journal or conservation closure.

The latest maintenance extension retains reset's clock before its getter, saved
next/current slots before fresh key reads, and clear's handshake→slots/puts→peer-put
order. Timers retain strict `> MAX`, the fresh keepalive-flag getter, caller-jiffies
before guards and duplicate-clear acquire/put. Clear-work recording precedes append;
record failure skips it. No timer-detachment, ownership or successful-clear premise
is added. Enqueue cleanup, saved scans, setter rereads and malformed/duplicate
cleanup IDs likewise retain earlier effects when later accesses Stop.

**Failure prefixes.** Original-run-conditioned equations, not accepted witnesses,
retain six events before session birthdate-clock failure; allocation/write before
peer cache-clock failure; five accesses before receive queue-record failure; four
before handshake-completion clock failure; one peer read for cache-miss/keepalive
allocation failures; initial key read/no write for empty bitmap; pending-timer read
after caller-read success and before jitter failure; MAC read/write before age
failure; and IPv4 read/write before reset-clock failure. Refcount rejection can
follow a write; release events occur only after successful final puts. The eager
timer-guard getter precedes `andM`. Safe prefixes imply neither delivery nor ownership.

**Historical accepted reference findings (through `7a92672`).** An eight-operation mirror run created 28 peers, started a stepped dump, deleted wg0,
created a new wg0 with 27 replacement peers, then received a chunk. The cursor retained raw slot 26, old identity 27,
with two references. Continuation cleanup instead released replacement identity 55, with one reference, removing it while
the peer list and public-key table still name slot 26. The received message is the already queued first chunk;
continuation generation performs the destructive put. This is reference retargeting and table incoherence, not resurrection of identity 27.

The guest rejects deletion with a pending dump (`wg_delete_with_dump_pending`), as the W1/W2 design requires.
`Env.wgDelete` then checked worker idleness but omitted that guard; `c047e64` restores it, including queued DONE chunks. C retains `ctx->wg`; the mirror resumes a Boolean-held cursor against the current device.
This was an accepted-mirror domain bug, not evidence of a Linux lifetime bug. Its explicit non-placeholder records are synthetic, not a fresh capture.
The historical replay checked five runner checkpoints, their count and original JSON equality.
The current replay instead checks the accepted pre-delete boundary and exact original/observer rejection at operation 3. The kernel-reduced
`stale_cursor_retargets_replacement` separately exercises `wgGetDeviceDone`; the historical full replay reached the bad put through dump-resume cleanup.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r2-stale-dump-cursor |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/LifetimeSafety/Replay.lean
capped -- scripts/in-bundle scripts/proof-gate
```

A second historically accepted eight-operation variant gave replacement peer 26 an IPv4 `10.0.0.0/8` binding before the stale continuation released it.
The final checkpoint follows the actual device root: the prefix still names slot 26 while resident identity 55 is absent.
It previously checked eight checkpoint emissions, five specified projections and original-runner JSON equality, using explicit synthetic records.
The current check likewise rejects operation 3 before replacement allocation. The old accepted run ruled out unconditional owner-residency invariants on that mirror; it neither resurrects identity 27 nor alone proves packet misrouting
or disagreement with insert/remove history. The historical input recipe is unchanged; its current accepted domain has changed.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r2-stale-dump-cursor-orphan |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/LifetimeSafety/ReplayOrphan.lean
```

**Remaining obligations.** Initialized outer Runner composition remains open.
The complete dispatcher, literal socket wrappers and exact syscall postworkers
now preserve AuditInv, including actual resident scans and namespace cleanup.
BatchTrials retains its conditional entry contract; audit markers derive that
invariant at each actual filter entry reached through these callers.
Activation.run uses plain condResched callbacks and introduces no nested
consistency trials; flood and receive-worker callers carry nestedReschedAudit.
The full FS frames and taskWorkRun still do not themselves execute queued cleanup;
the separate Env cleanup observer covers that body at the syscall's original
postworker cut. These local contracts do not assert failed-World invariants or
supply initialized Runner entry facts. Complete wgSetDevice, all seven dump calls
and the three WG lifecycle calls are now composed through their actual wrappers.
Saved scalar
affiliation and reference credits are stronger separate properties:
dangling/aliased IDs can Stop after safe accesses. C initializes cache/handshake before incrementing the peer counter;
the mirror increments/inserts first. Proofs follow the mirror; this difference
alone is not a lifetime counterexample or C simulation.

**Effort.** Counts are per checkpoint, not an inferred campaign total. Earlier
caller checkpoints used roughly 6–25m and 4–19 invocations each. Historical cursor
replays and both current rejection checks each took under one second.

| Checkpoint | Capped invocations: passed / failed | Elapsed |
| --- | --- | --- |
| TX staging | 14: 2 / 12 | 24m44s |
| Receive completion/poll | 14: 3 / 11 | 23m50s |
| Saved scans and initial ten-call socket family | 20: 3 / 17 | About 43m |
| Staged IPv4 send | 8: 5 / 3 | About 8m |
| Encryption worker | 4: 2 / 2 | About 6m |
| TX completion/worker | 6: 1 / 5 | 21m03s |
| Five-call handshake family | 7: 1 / 6 | About 15m |
| Six-call handshake send family | 6: 2 / 4 | 7m39s |
| Four-call cookie family | 5: 2 / 3 | 11m41s |
| Handshake receive/worker and thin ingress | 7: 2 / 5 | 20m06s through full-build collection |
| Concrete Batch scheduler and separate trials | 18: 5 / 13 | 29m41s through full-build collection |
| Allowed-IP list/removal access | 6: 3 / 3 | 17m17s through scoped-target collection |
| Key maintenance and expired timers | 5: 3 / 2 | 20m07s through collected full-build result; component/scoped/full targets 144/226/334 |
| Inline flush and peer removal | 5: 3 / 2 | 9m53s through collected full build; 14m57s ownership including recovery freezes; component/scoped/full 158/227/340. Two ordinary elaboration failures; two read-only reviewer capacity interruptions caused freezes/all-dirty snapshots, with no build interrupted. |
| Socket/device controls | 6: 4 / 2 | 18m20s from token acceptance through full-target collection; 19m18s total token ownership; component/scoped/full 160/229/349. Two ordinary proof elaboration failures, no cap/interruption; all exits collected. Coordinated gate, fresh kernel replay, default build and 114 unit tests pass. |
| Device creation/destruction/deletion | 14: 2 / 12 | 18m58s from grant 11:42:06 through full-target collection at 12:01:04; 22m43s total token ownership. Scoped/full targets 233/362, R2 176 exports. Twelve ordinary elaboration/normalization failures, no cap/interruption; all exits collected. Independent frozen review and coordinated gate, fresh kernel replay, default build and 114 unit tests pass. The coordinator mistakenly overlapped the cached default build (0.033s) with kernel replay; both were capped and both exits collected, then serial validation resumed. |
| Insertion and peer configuration | 18: 8 / 10 (17 builds: 7 / 10; one passing scope/census check) | 33m38s from grant 13:02:01 through final full-result measurement 13:35:39; 36m19s ownership through handback 13:38:20. Scoped/full targets 238/372; R2 182 exports, total 386 declarations. The insertion-only full checkpoint passed 369 jobs before configuration. One invocation hit deterministic heartbeat limits in monolithic peer-command proofs; source stages replaced that proof shape. Nine other invocations failed ordinary elaboration/normalization. No cap/interruption, all exits collected; independent frozen source/documentation review clear. Coordinated gate, fresh kernel replay, default build and 114 unit tests pass sequentially; frozen Lean hashes unchanged. |
| Local strong-FS frames and lifts | 6 calls: 5 builds (4 / 1) and one passing scope/census check | 16m52s from grant 13:44:39 through full-result collection at 14:01:31; 19m31s ownership through handback 14:04:10. Compatibility/scoped/full targets 90/242/376. One ordinary migration failure truncated the legacy iterator-count statement and omitted arithmetic hypothesis arguments; independent review found the same statement issue. Both were restored without changing the API. No cap/interruption, all exits collected. Three grouped exports over six original calls; independent frozen source/documentation review clear. Coordinated gate, fresh kernel replay, default build and 114 unit tests pass sequentially; frozen Lean hashes unchanged. |
| Complete device configuration | 9 calls: 7 builds (3 PASS / 4 ordinary FAIL), then two scoped checks (FAIL / PASS) | 20m51s from grant 14:39:57 through full-result collection 15:00:48; 24m55s ownership through handback 15:03:52. Component/scoped/full targets 178/246/386. Four ordinary elaboration/normalization failures; the first scoped check failed on four trailing spaces, corrected before the passing scope/census check. Those whitespace-only changes postdated the worker full build and pass the coordinated rebuild. No cap/interruption; all exits collected. Existing three grouped exports extended, retaining 185 R2 / 393 total declarations. Independent frozen source/documentation review is clear; its Markdown effort-table separator finding is fixed. Coordinated gate, fresh kernel replay, default build and 114 unit tests pass sequentially; all eight frozen Lean hashes are unchanged. A separate seven-minute source-coverage audit of the committed R2 foundation found no defect in its inspected local contracts. No runtime change or replay. |
| Complete FS migration and dispatch/task work | 7 calls: 6 builds (3 PASS / 3 ordinary FAIL) plus one passing scope/census/compatibility check | 10m15s from grant 15:10:50 through full-result collection at 15:21:05; 11m51s ownership through handback 15:22:41. Compatibility/scoped/full targets 109/251/391. Failures involved missing projected refcount contracts, replacement of the snapshot-specific eventfd proof tactic, task-only modification framing and generic view universe inference. All 347 legacy signatures are unchanged; three new exports give 188 R2 / 396 source declarations. No cap/interruption or runtime change; all exits collected. The review finding that the register row prematurely described the new extension as current is fixed. Independent frozen source/documentation review is clear. Coordinated gate, fresh kernel replay, default build and 114 unit tests pass sequentially; all ten frozen Lean hashes are unchanged. |
| Complete Netlink dump family | 14 calls: 13 builds (4 PASS / 9 ordinary FAIL) plus one passing scope/census/compatibility check | 30m09s from grant 16:07:50 through full-result collection clock 16:37:59. Canonical/component/scoped/full targets 45/176/255/401; seven original calls, three new exports, 191 R2 /403 source declarations. Failures were ordinary elaboration/normalization and deterministic heartbeat exhaustion in monolithic serialization/chunk proofs; source cuts and checked continuation-sharing replaced that proof shape without changing premises. No cap/interruption or runtime replay; all exits collected. Exact nine-file scope, whitespace, both legacy theorem-signature sets and the c047e64 mirror comparison pass. Independent frozen source/export/documentation review and sequential coordinated gate, fresh kernel replay, default build and 114 unit tests pass; all seven frozen Lean hashes remain unchanged. Token returned at 16:39:42 (31m52s ownership). |
| Reached consistency-trial audit | 10 capped calls: nine builds (3 PASS / 6 ordinary FAIL) plus one passing scope/census check | 17m23s from grant 17:10:31 through full-result collection at 17:27:54. Component/scoped/full targets 185/260/403; five new exports, 196 R2 /408 source declarations. Three initial elaboration failures were followed by two full-import failures from a duplicated Lean-generated matcher helper and one insufficient-normalization failure. Normalizing the fixed worker list before local `grind -matchEqs` resolves the collision without changed statements, dependencies or global settings. All ten exits collected; no cap kill, interruption or runtime replay. The 0.06s scoped check passes exact six-file scope, all four Lean hashes, unchanged prior statements/helpers, 408 declarations, whitespace and mirror equality to 43c7549. Four Lean files and two docs; independent frozen source/export/documentation review is clear, including the local tactic repair. Sequential coordinated gate, fresh kernel replay, default build and 124 unit tests pass; all four frozen Lean hashes are unchanged. Token returned at 17:31:59 (21m28s ownership). |
| Deferred workers and timer dispatch | 15 calls: 14 builds (5 PASS / 9 ordinary FAIL) plus one passing scope/census/compatibility check | 26m29s from grant 17:37:28 through full-result collection at 18:03:57. Foundation/worker/timer/scoped/full targets 139/191/194/266/409; fifteen original calls and three grouped exports. Failures involved leaf-loop framing, captured-map normalization, post-scan contract matching and deterministic heartbeat exhaustion in a monolithic timer erasure. Literal source cuts and shared pure scan/fold functions closed the latter without changed behavior or premises. No cap/interruption or runtime replay; all build exits collected. The exact eleven-file scope, all nine Lean hashes, 75 unchanged legacy theorem signatures, prior terminal statements, 411 declarations (199 R2), whitespace and mirror equality to 43c7549 pass. Independent frozen source/export review is clear; review clarified predicate misses versus absent-map slots. Sequential coordinated proof gate, fresh kernel replay, default build and 124 unit tests pass; all nine frozen Lean hashes remain unchanged. Token returned at 18:05:55 (28m27s ownership). |
| Remaining environment callers | 17 calls: 16 builds (5 PASS / 11 ordinary FAIL) plus one passing check | 30m45s from grant 18:10:58 through full-result collection 18:41:43. Control/traffic/batch/scoped/full targets 205/207/209/273/416; fifteen originals and three grouped exports, 202 R2 / 414 declarations. Ordinary failures involved leaf framing, import/layout, constructor equality normalization, and deterministic heartbeat exhaustion in monolithic batch erasure. A source-only ForInStep item cut closed the original equation by rfl without changed behavior or premises. No cap/interruption or runtime replay; all build exits collected. Independent frozen source/export review is clear; stale environment-limit wording is corrected to the remaining syscall/initialized Runner scope. The capped exact fifteen-file scope/census/whitespace/mirror check passes, with all 218 compatibility theorem signatures and 199 prior R2 terminals unchanged. Sequential coordinated proof gate, fresh stock kernel replay, default build and 124 unit tests pass. Token returned at 18:43:29 (32m31s ownership). |
| Complete syscall callers | 11 capped calls: nine builds (5 PASS / 4 ordinary FAIL) plus two passing checks | 11m55s from grant 18:49:32 through full-result collection 19:01:27. Wrapper/compatibility, dispatch, syscall, scoped/full targets 228/239/240/277/420; all 34 typed constructors (35 dispatch arms), three grouped exports, 205 R2 / 417 declarations. Ordinary failures involved record layout, macro forward-name resolution, callback-family reduction, the dump socket lift and branch contradiction normalization. Calls 1/2/4/6 failed; 3/5/7/8/9 passed; call 10 passes exact scope/census/signatures/whitespace/mirror and all six Lean hashes; call 11 confirms the documentation corrections, whitespace and unchanged Lean hashes. All ten compatibility signatures and 202 prior R2 terminals are unchanged. No changed premises, cap kill, interruption or runtime replay; all eleven exits collected. The reviewer found stale current declaration-table counts and two syscall-open scope clauses; all are corrected. Independent frozen source/export/documentation review is clear; a separate lower/Env/syscall source-coverage audit found no defect in its inspected surfaces. Sequential coordinated proof gate, fresh stock kernel replay, default build and 124 unit tests pass. All six frozen Lean hashes remain unchanged. Token returned at 19:08:01 (18m29s ownership). |

Earlier monolithic IPv4 proof search failed at heartbeat limits; explicit source
tails replaced it. An earlier tactic loop was deliberately stopped by its verified
PID. Scheduler call two failed because a wrapper moved while its dependency graph
was running; later builds froze inputs until exit. Its other twelve failures were
ordinary elaboration failures. The allowed-IP coordinated gate failed on ambiguous
legacy/canonical `getNode_sameKernel`; explicit canonical selection repaired it.
The latest maintenance tranche had two ordinary elaboration failures, no cap or
interruption, 20m07s to full validation and 21m53s total ownership; all five logs
were removed. Earlier scheduler and allowed-IP ownership totals were 30m55s
and 17m56s respectively.

The socket/device review qualified the reset after a negative open result as
`wgUp`’s continuation; `wgOpen` itself does not reset running. The lifecycle
review qualified fresh-epoch registration as successful creation, retaining
existing-device/refusal alternatives, and corrected one missing list comma.
Reviews deleted an unused impossible KDF-failure premise; corrected no-device
`modifyDev` framing, saved-stamp/cache scope, original-run versus accepted-domain
wording and an overbroad docstring; and shared a conditional law in `Prefix`.
They preserved legacy frame signatures and fixed duplicate matchers, buffer-refusal
access scope, false-session versus Stop completion, duplicate-ID wording, stale
scheduler closure/status counts, and timer-detachment/dispatcher wording. No
unresolved source/premise defect remains in the reviewed components.

**Ranked mirror suggestions.** (1) If pending-dump deletion is admitted again,
retain the actual device lifetime in the cursor as C does: altitude-preserving,
requiring separate validation. Current rejection is fixed by `c047e64`.
(2) Keep named allocation/deletion/same-object update boundaries: altitude-preserving.
No production history field is proposed.

## R3 — cryptokey routing (in progress)

**Original versus proved.** The charter concerns configuration history and RX/TX
cryptokey identity binding. Current [terminal contracts](../Leanux/Proofs/WG/CryptokeyRouting/Statements.lean)
prove represented trie operations and initialized finite histories of the listed
original calls, not the enclosing configuration or packet claim.
No R3 Rule Zero counterexample or changed charter conclusion is asserted.

| Model | Abstraction and refinement boundary |
| --- | --- |
| `Prefix`, `Tree`, flat `Winner` | Bounded width-parametric Patricia geometry and independent longest-prefix binding specification; `commonBits_correct`, `prefixMatches_correct`, `choose_correct`, `pureTree_lookup_correct`. Strict CIDR growth bounds depth by width+1. |
| `Store.RepAt`, `ForestRep`, `Context` | Exact node values/backlinks with unrelated store entries allowed; original placement and `original_findNode_lookup_correct` derive traversal and the 130-step bound. `RepAt` alone does not supply external root linkage. |
| Pure `Insertion` | Canonical-prefix replacement, validity/compression and old/new ID accounting; `pureTree_insert_lookup_correct`. Exact overwrite retains the old ID/raw address; new requested/intermediate nodes use consecutive IDs. |
| `InsertionCases`/`InsertionDispatch` | Reuse all staged empty/exact/graft source contracts; `original_add_all_cases`, `original_insert_all_cases` and `original_insert_longest_prefix` derive placement alternatives and actual-root lookup. |
| `InsertionMetadata`/`Entries`/`Coherence`, `RoutingInvariant`/`InsertionRouting` | Exact source peer-map/frame effects plus binding-ID entry correspondence derive resident coherence and bounded raw owners; `original_insert_routing_preserved`, `original_insert_coherent_peer_maps`, `original_insert_refusal_coherent` and `original_removeByPeer_routing_preserved` retain the combined invariant. |
| `Removal`, `ContextRemoval` | Pure `eraseId`/compaction, exact entry filtering and ID subsequence; `pure_removal_structure`, lookup and locality contracts. Under compression/Nodup, at most two IDs retire. Pure absent-ID identity is not an original absent-target no-op claim. |
| `RemovalSource`, raw endpoint/store layers | All-input original loop equation and exact local mutation endpoints, including post-free parent-tail continuation; no representation or owner residency is inferred from stored tags. |
| `RemovalContext`/`Transport`/`Cases`/`Dispatch` | Membership focus plus represented contexts derive all seven cases; `original_removeStep_forest_total` and `original_removeStep_forest_properties` prove actual execution, both-family erasure, retirement and full frames. |
| `RemovalLists`/`Loop`/`Peer` | Explicit resident-only list coherence and fixed saved-list induction; `original_removeByPeer_forest_total` and `original_removeByPeer_forest_properties` and `original_removeByPeer_then_findNode` connect complete original removal to owner filtering and lookup. |
| `RoutingView`/`Lifecycle`/`Initial`, `FlatHistory`/`RoutingHistory` | Option-valued routing/list projection; original create/refusal and raw-release preservation; original configured fixture; canonical flat updates without node IDs and finite actual-call induction. `original_initialized_routing_history` derives coherence/agreement, and `original_initialized_history_findNode` links reached-root source lookup to the flat winner and actual raw node owner. |
| `AddressBounds`/`ConfigurationInputs`, `ClearWalk` | Actual UInt8/parser address shape and original setAllowedip guard cuts; normal insertion/routing composition; exact root-list source factor and extensional normal-completion coverage with full list-only frames. `parsed_setAllowedip_bounded_call`, `parsed_setAllowedip_routing_preserved`, `original_rootRemove_lists_normal`. |
| `ClearSnapshot`/`ClearEndpoint`, `RoutingCall.clear` | Fixed original nodes/current submap with retained list provenance and exclusions; complete original normal clear derives empty represented trees/lists, exact outside fields and seq+1. `original_free_routing_endpoint`, `original_free_then_findNode`; existing initialized history/lookup exports now include clear. |
| `RoutingRetains`/`Completions`, concrete send/socket/handshake/flush frames, `RoutingAcquire`; configuration tail/removal/update observers | Deletion-permitting routing frames; actual whole-setAllowedip/removal events and flat folding; exact acquired-peer update through replacement/removal, attributes and complete tail. Lookup/create residency is separately derived. Unconditional erasure remains separate from entry-conditional safe-prefix and normal reached-state agreement. |

[AGENT 2026-10-13] Use width-parametric arithmetic, one Patricia tree and pure
insertion, with contexts as structural paths rather than another executable
algorithm. Retain raw addresses/allocation order and freshness across the whole
node store, including unrelated/opposite-family entries.
[AGENT 2026-10-14] Factor established insertion cases into common dispatch; put
pure ID erasure/compaction and context locality in separate layers. Keep removal's
source factor low-dependency, importing only original AllowedIps, for reuse by R2.
Expose the actual post-target-free parent tail so source reductions stay local.
Transport exact endpoints through context/forest representation, then carry explicit
resident-list coherence through the original saved loop; do not assume initialized
history or strengthen raw owner labels to resident ownership.

[AGENT 2026-10-14] Strengthen the common `Inserted` contract with source-derived
peer-map/device frames, reusing dispatch. Normalize fresh append only after
coherence proves fresh-ID absence; keep owner-frontier bounds separate from
owner residency so orphan raw labels remain representable.
[AGENT 2026-10-14] Retain device/list absence in the lifecycle projection and
canonical prefix bits/raw owners without node IDs in the flat history. Use typed
v4/v6 calls with actual normal returns and reached-input insertion bounds/residency;
derive intermediate invariants rather than placing them in history constructors.
[AGENT 2026-10-14] Pin the actual private parser through the existing proof-side
name helper, deriving address shape from its shared Option byte list. Factor the
original root-list loop at its ForIn carrier and use extensional frontier coverage
on normal empty-stack return; do not identify its order with subtree enumeration
or add owner residency/fuel sufficiency to suppress Stops.
[AGENT 2026-10-14] Compose full clear against a fixed original node snapshot,
retaining a predicate on surviving resident-list IDs through list filtering and
node-only erasures. This supports both saved-root walks without equating traversal
orders or requiring a representation over the partly erased current node map.
[AGENT 2026-10-14] Use a survivor-list routing relation for silent source calls,
permitting peer deletion while retaining nodes/table/frontiers. Journal whole
setAllowedip completions and derive semantic validity from actual calls; use
stronger cached-peer frames only where source getters/setters require them.
Share the original tail factor and existing send-frame matcher environment.
[AGENT 2026-10-14] Extend the completion journal with an explicit primitive sum,
placing removeByPeer events inside peerMakeDead before later cleanup/flush effects.
Reuse socket/handshake source factors and prove deletion-permitting concrete frames;
keep lookup/create residency separate until public-command preflight composes.


**Insertion boundary.** Valid representation, unique IDs, whole-store `NodesBelow`
freshness, bounded address/CIDR and a resident target peer are explicit inputs.
Original placement derives exact/empty/stopped cases; callers do not assume the
desired output. Every bounded-input normal return is classified. First allocation
refusal leaves `add`'s Kernel unchanged; second refusal consumes one ID, frees its
node and filters that ID from every peer list. It is not whole-World rollback.
`insert` increments sequence before success or either refusal. Record Stops and
invalid-input returns are outside this classification. Exact replacement filters
every peer list then appends once to the target; fresh branches only append to the
target, without sanitizing arbitrary dangling lists. The common success contract
now includes those raw peer-map effects and a frame allowing only nodes, peers,
trie metadata and nextNode to change. `RoutingInvariant` adds both actual family
roots, validity/compression/Nodup, resident list coherence and node/peer/owner
frontier bounds. Input coherence derives fresh-ID absence and normalized list
updates. Both normal refusals preserve node/list contents pointwise under that
invariant, retaining the sequence increment and any consumed ID. Only the requested
peer must reside; other owner labels may be orphaned.

**Removal boundary.** Source equality retains branch recording, `listDel` before
target lookup and both continues. Binary removal clears the owner and retains the
node; leaf/unary removal erases it. Nonroot removal detaches first, reads the updated
parent owner/sibling, frees the target, then freshly rereads the parent for collapse.
Raw cases retain short-array behavior, optional absent siblings and later Stops;
parent tags alone do not assert actual root selection.
`ForestRep` plus compression, Nodup and explicit target membership derives residency,
actual linkage and every local separation premise; encoded widths separate families.
The resulting original step has exact peer-list filtering, pure `eraseId` in the
selected tree, the other family retained, disappeared IDs absent, unrelated node
entries preserved and full Device/Kernel frames. Validity yields post-findNode
agreement with the surviving flat-list winner. No target-owner residency is needed.

`ResidentLists` says each resident peer has a duplicate-free list whose membership
is exactly its owned forest entries. It imposes no owner residency for orphan labels.
`OwnedIds.tail` proves later saved bindings survive prior erasures, including parent
collapse; the source executes the original captured list, not a reread list.
Complete `removeByPeer` retains the first getter/empty branch, sequence increment
iff that list is nonempty, original forIn and final false record only on the
nonempty path. It empties the target list, preserves resident coherence and filters
exactly that peer's entries in both families, with aggregate retirement/outside
frames. Its totality is conditional on the input representation/coherence; normal
source execution is a conclusion, not a premise chosen to suppress missing nodes.

**Finite-call boundary.** The original configured fixture establishes the invariant.
Normal `peerCreate` refusal retains the routing projection; success returns the old
peer frontier and installs an empty list. Owner bounds make that list coherent
without requiring old owners to reside. Normal raw `peerPut` may delete a peer while
retaining its trie labels. Histories chain actual normal create/insert/removeByPeer/
peerPut/free executions and actual returns; insertion alone supplies bounded arguments
and a resident target. Removal residency follows from its original getter. Flat
insertion replaces a canonical prefix, removal filters its owner, and creation,
release and insertion refusals leave the flat tables unchanged; normal clear empties
both flat tables. Both insertion
refusals still retain their distinct sequence/frontier effects in the source
contracts. Final original findNode is total for bounded queries at the actual
family root and returns a flat-history winner with the same raw store owner.

**Parsed local input and clear boundary.** The original private parseAllowedIp
builds address and length from the same optional UInt8 list. Its fold is bounded
by 256^length, including zero/leading-zero inputs, without a hex-decoder fidelity
premise. Malformed entries, missing fields and AF overrides retain source behavior.
Original setAllowedip either normally rejects with EINVAL and unchanged Kernel or
reaches the actual bounded v4/v6 insertion after its guards; the cut retains guard
steps. Entry routing/flat invariants and target residency remain explicit in this
local composition. Negative insertion returns keep their sequence/frontier effects.

Original rootRemovePeerLists pushes left then right (thus processes right first).
Its all-input source equation retains branches, missing-owner/list Stops and the
exhaustion Stop. Normal completion reaches an empty pending stack; frontier closure
then covers every represented subtree ID without proving fuel sufficiency. Resident
lists exclude those IDs afterward. The complete node map and every other Kernel,
Device and peer field are preserved, with only allowed-IP lists hidden by the frame.
Resident-list ownership follows from RoutingInvariant; raw owners need not reside.
Complete original WG.free saves both roots before resetting them and incrementing
sequence, then runs root4 and root6 phases with intervening subtree/freeNode calls.
The proof retains original node values and surviving-list provenance/exclusions;
successful getters recover the saved children even after earlier erasures. Normal
completion derives empty resident lists and an empty represented forest. Its full
Kernel/device frame preserves every other field and allocation frontier; peer
absence and complete records are exact except for emptied lists. Current nodes
are only a value-preserving submap, not necessarily physically empty. Totality is
not asserted: absent raw owners or erased references may still Stop. The clear
history constructor carries only actual normal execution, never output coherence.

**Completed allowed-IP prefix.** Every whole setAllowedip normal return emits
its exact signed result and entry/exit routing views. A zero return applies
flatInsert; ordinary negative returns leave the flat table unchanged, retaining
prior completed updates and actual source sequence/frontier effects. The original allowed-IP loop preserves
its target through exact insertion/refusal endpoints, then permits deletion through
real keepalive/staged-send and peerPut cleanup. Unconditional erasure covers malformed
attributes and Stops. With explicit entry routing/residency and local address shape,
semantic prefix validity is derived from source calls; normal returns also derive
current routing/flat agreement. A later Stop retains earlier valid completion
events but supplies no failed World or output invariant. The semantic event predicate
alone does not assert physical adjacency; actual source composition and concrete
silent frames provide the connection. No affiliation or reference-credit premise
is needed for these trie/list frames.

The acquired-peer update now also covers REMOVE_ME, preshared-key and endpoint
updates and REPLACE_ALLOWEDIPS. A nested removeByPeer event records actual routing
removal before hash/death/flush work; it does not claim whole peer-object removal
completed. Source-derived socket, handshake, key-clear, timers and bounded drain
frames retain routing on normal returns without a drain-success, reference-credit
or affiliation premise. Actual lookup and creation/refusal separately derive the
returned raw-slot residency; they establish no public-key identity association.

**Remaining obligations.** Public setPeerCmd preflight/acquisition composition is
still open. Its attempted tagged preparation equation did not close within this
slice's elaboration budget; the uncompiled draft was removed, without replacing
it by a target-residency or desired-output premise. The compiled acquired stage
retains explicit entry routing/target/address shape. Extend to enclosing peer/device
configuration and completed clear observations. A failing clear has no returned
World or successful completion marker; earlier partial mutations are outside a
completed-call history. Propagate local parser shape through parsePeer/config/operation
and public parseTrace, including bare/create/delete intervals and other Netlink
mutations. Literal contiguous histories cannot span unobserved guards/helper effects.
Connect packet paths to authenticated allocation identity; raw peer labels and
longest-prefix lookup alone establish no ownership.
The historical R2 orphan recipe constrained the former accepted domain; `c047e64`
now rejects it before deletion. It is not a current R3 misrouting counterexample.

**Effort.** Arithmetic, pure tree, original traversal and pure insertion used
5/6/20/13 compile invocations. Subsequent counts remain separate:

| Tranche | Capped invocations: passed / failed | Elapsed |
| --- | --- | --- |
| Empty-root insertion | 12; outcomes not separately tallied | 11m44s |
| Placement | 21, including a failed monolithic child architecture | About 30m |
| Staged child replacement | 19; outcomes not separately tallied | About 18m |
| Arbitrary-depth empty child | 8: 5 / 3 | 11m49s |
| Exact-prefix replacement and list deletion | 21: 7 / 14 | About 18m |
| Selected-root graft endpoints/rollback | 40: 6 / 34 | 35m28s |
| Selected-root successful refinement | 7: 4 / 3 | About 8m |
| Arbitrary-depth nonempty graft | 30: 4 / 26 | 36m47s |
| Unified insertion dispatch | 11: 8 / 3 | 12m08s |
| Pure removal and context locality | 9: 6 / 3 | 9m05s validation; 10m16s writer-token ownership |
| Local removal source and endpoints | 7: 2 / 5 | 14m17s through source freeze; 14m49s through handoff receipt |
| Nonroot removal and parent collapse | 9: 3 / 6 | 16m06s through frozen handoff preparation; 12m48s through scoped-target collection |
| Represented forest and coherent peer removal | 29: 14 / 15 | 43m01s through final full-target collection; 47m57s writer-token ownership |
| Insertion metadata, coherence and routing invariant | 15: 9 / 6 | 24m44s through collected full build; 25m28s writer-token ownership; scoped/full targets 130/339; six ordinary elaboration failures, no cap/interruption |
| Initialized finite routing histories | 15: 7 / 8 | 23m15s from first worker clock 09:24:41 through final full-target collection clock 09:47:56; 24m21s through token return at 09:49:02; scoped/full targets 150/347; ordinary elaboration failures, no cap/interruption |
| Parsed allowed-IP and root-list-clear checkpoint | 27 builds: 7 passes / 20 ordinary elaboration failures; scoped/full targets 154/358 | 27m28s from grant 11:08:10 through full-result collection clock 11:35:38; independent frozen review clear; 28m58s writer-token ownership through handoff clock 11:37:08; no cap/interruption or runtime change |
| Full normal clear and finite history | 11 calls: 10 builds (five passes / five ordinary elaboration failures) plus a passing scoped check; scoped/full targets 156/367 | 15m52s from grant 12:37:14 through measured full-result collection 12:53:06; 17m45s writer-token ownership through handback 12:54:59. Independent frozen review and coordinated gate, fresh kernel replay, default build and 114 unit tests pass. No cap/interruption or runtime change; all exits collected. |
| Whole allowed-IP completions and peer tail | 17 calls: 16 builds (7 passes / 9 ordinary elaboration/normalization failures) plus one passing scope/census check; scoped/full targets 210/382 | 20m15s from grant 14:09:16 through full-result collection clock 14:29:31; 24m11s writer-token ownership through handback 14:33:27. Four new exports, 86 R3 /393 source declarations. No cap/interruption or runtime change; all exits collected. Independent frozen review is clear after correcting the report's zero-return wording: flatInsert may be idempotent. Coordinated gate, fresh kernel replay, default build and 114 unit tests pass sequentially; frozen Lean hashes are unchanged. |
| Acquired-peer removal/update completion | 30 calls: 29 builds (8 PASS / 21 ordinary elaboration/normalization FAIL) plus one passing scope/census check; final scoped/full targets 278/397 | 30m40s from grant 15:30:16 through final full-result collection clock 16:00:56. Four exports, 90 R3 /400 source declarations. No cap/interruption; all exits collected. The complete acquired stage and concrete flush/acquisition foundations compile; repeated preflight continuation-normalization failures left whole setPeerCmd composition open. No runtime change/replay. Independent frozen review and coordinated gate/fresh replay/default/unit validation pass. Token returned at 16:02:40 (32m24s ownership). |

The represented/loop tranche split into 17 single-step calls and a 12-call
continuation; its fifteen failures included two heartbeat failures. Final scoped/full
builds passed 125/332 jobs; no runtime recipe changed. Earlier broad child/source
proofs failed at heartbeat limits; exact source cuts, including the final return,
and explicit metadata projections closed without mirror changes. Raising the
nonroot metadata heartbeat did not help; projection reduction passed at default.
The local-removal third build failed with its `/tmp` diagnostic read-denied by nono;
that diagnostic is unavailable and the owned file was deleted without sandbox/global
changes. Failed patch/relocation applications made no affected-file changes and were
not build invocations. Two later read-only planning turns disconnected after pure
removal validation; all four dirty worktrees were snapshotted before subsequent work.
The finite-history review separated the pure flat model from Runner/lifecycle imports,
corrected a stale open-scope sentence and clarified that raw peer IDs remain while
node IDs are omitted. One additional read-only whitespace check ran directly and
passed; it was not a capped build/check invocation.
The completion-tail review corrected “changes the flat table” to “applies flatInsert”: identical successful reinsertion may leave the table equal.
No build was interrupted. Reviewed `freeNode` residency, root linkage versus values,
normal returns versus reachability, endpoint versus event order, and Stop versus
successful-World wording were corrected. A source-factor observation was withdrawn
after rereading its final `rfl`; duplicated effort/status text was removed.

**Ranked mirror suggestions.** None: operational arithmetic and integer address
encoding already permit refinement. C byte-layout correspondence remains informal;
proof-side factors did not require a production restructuring.

## R4 — queue, poll and delivery-order components (in progress)

**Original versus proved.** The charter asks for ordering under every accepted
schedule and no silent loss/duplication. Current [terminal contracts](../Leanux/Proofs/WG/DeliveryOrder/Statements.lean)
prove physical-ring and local poll/source-scheduler properties. The chronological
post-GRO reading is false; joint pipeline conservation remains open.

| Model | Abstraction and refinement boundary |
| --- | --- |
| `RingGeometry`, `RingSteps` | Exact `ringOf` from stale physical slots plus live FIFO; original full/peek/count/items and produce/consume laws, every batch and wrap. `represented_ring_*` derive successor geometry; size zero has separate laws. |
| `RingJournal`, `RingMap`, `RingOccurrences` | Finite offers/polls satisfy admitted=consumed++live and consumed=retired++stale. Initialized conservation and tagged erasure permit repeated payloads; each offer, even refusal, gets a fresh ordinal. |
| `RingSource`, RX/TX journals | Installed-mutation histories replay original ring operations. Entry/worker erasure is unconditional; prefix refinement links replay to the actual cell only on normal return. On Stop only an existential replay ring remains. |
| `PrevQueue`, `RxQueueView` | Contents include cached peek; original queue laws and concrete receive-cell frames allow peer deletion. Malformed nonstub empty queues retain their invariant Stop. |
| `RxPollPrefix`/`Order`, projected `GroState` | Original outer-drop observations, buffered offers and callback entries; `original_poll_removal_prefix` and selected callback-prefix/completion contracts. |
| `RxPollTags`, `RxPollProjection`, `RxPollProvenance` | Buffered tags are a subsequence of removed occurrences; direct result/World/Stop/log projection and concrete stack frames derive callback origins. Separate erasures alone would not prove log agreement. |
| `SourceScheduler`, `RxRingScheduler`, `RxRingTrials` | Concrete RX scheduler refinement discharges its callbacks; original trial decisions/ordered filter and safe trial prefixes remain separate from committed history. |
| `Framing/PeerBorrow`, `RxBorrow` | Actual lookup acquisition derives positive old refcount; adjacent repayment restores the full outside-peer Kernel and every complete peer record pointwise. Existing access observers retain failed prefixes. |
| `TxDisposition*`, `Logged/ProjectsUnder` | Joint actual admission/publication/removal/completion cuts; exact createData access/ring projection and allocation-conditional full-step access projection. Source cuts and normal EPIPE queue/DEAD-head/ring, ENOSPC packet-absence and actual DEAD-step disposal endpoints. Publication queue retention spans CPU/work updates; arbitrary-schedule transport is separate. |

[AGENT 2026-10-13] Use symbolic filling/pointwise slot algebra; retain complete
receive cells with peer identity and permit deletion. Observe drop, completion offer
and callback entry at actual boundaries with failed prefixes, tagging local ordinal,
skb and bytes. Derive concrete stack frames and direct observer projections; retain
`GroSafe` and name selected-order results separately from the false chronology claim.
[AGENT 2026-10-14] Separate tail-relative stale/live geometry, finite occurrence
journals and packet identity. Derive admission freedom independently of the old
`EnqueueResult` API. Observe installed RX mutations; defer enqueue emission only
across its final pure return. Share the payload-parametric RX/TX source core while
preserving RX interfaces, explicit callbacks and Stop replay. Share scheduler
control through parameterized proof bodies and keep copied trials separate; project
canonical scheduler frames into unchanged legacy signatures.
[AGENT 2026-10-14] Prove the adjacent source-lookup/reference-repayment cut before
the carrier ledger. Use full outside-peer Kernel equality plus pointwise complete
peer equality, avoiding irrelevant TreeMap shape obligations. Import the existing
WGBase proof environment to reuse generated source matchers; no legacy signature changes.
[AGENT 2026-10-14] Factor exact source continuations and project a joint disposition
observer directly to existing access/ring histories. Unconditional appended-suffix
laws cover simple focused helpers; full TX-step projection uses the existing entry
allocation invariant and concrete intermediate contracts for completion. This avoids
assuming allocation preservation at an arbitrary captured setter.
[AGENT 2026-10-14] Frame the publication interval with all peer TX queues and the
borrowed peer count. Derive count greater than one from the actual acquisition,
so repayment cannot delete a peer; no enqueue/publication-pid equality is needed.
Keep normal store/disposal endpoints separate from transport across later schedules.
[AGENT 2026-10-14] Close R4 over the receive-to-stack pipeline under accepted
schedules, together with the charter's named W7 transmit-drop characterization.
Transmit callbacks must preserve the required RX carrier invariant. Universal
outgoing staged/encrypt/socket conservation is additional scope, not a prerequisite
for the receive claim; existing conditional TX journal contracts remain as stated.

**W7 and physical fullness.** Two produce/consume pairs in the original size-1024
ring leave logical count zero but physical slots 0 and 1 occupied. The next 1024
guarded offers accept 1022 and refuse two, ending producer/head/tail at 0/2/0 with
exact accepted FIFO. The [W7 tier](2026-10-13-w7-full-ring-tier.md) corrected the
one-drop prediction that omitted the keepalive slot: Linux and mirror agree on
both `-EPIPE` drops. All producers precede consumption. The closed ring witness is
not refinement of that entire recorded run. The command below checks an
**eight-transmit scheduler regression**, not the 1024-item wrap or its two drops.
It rearranges captured records and adds synthetic end-of-wait bounds;
caller-clock migration is described above, not a fresh capture. The full-tier
operations are tracked in `corpus/w7-tier/w7_ring_wrap.json` (and the extra ENOSPC
case in `w7_ring_1025.json`), but their full hidden streams are not tracked here.
The original normal EPIPE endpoint now retains its queued item and DEAD head;
normal ENOSPC cleanup removes its packet slots. A normal txStep entered on that
actual DEAD queue head disposes the item without socket output. These are local
source-derived contracts. Transport of the refusal's item/mark across an arbitrary
intervening schedule remains open; neither replay nor pure ring geometry supplies it.

```sh
capped -- scripts/in-bundle bash -o pipefail -c 'python3 -B -c "import json; from evaluator.test_model_replay import W7_CRYPT_AHEAD, with_jiffies_end, with_timer_caller_jiffies; print(json.dumps(with_timer_caller_jiffies(with_jiffies_end(W7_CRYPT_AHEAD))))" | lake env lean --run Leanux/Proofs/Logged/Replay.lean'
```

**Source and conservation limits.** Positive geometry requires `t + stale.length < n`
and `stale.length + live.length ≤ n`; physical fullness is total occupancy `n`.
Retirement clears already consumed slots, not lost packets. Initialized journals
permit pending live contents and do not imply eventual consumption. Size zero
retains refusal/empty-poll coverage. Arbitrary-ring tag erasure is not freshness
relative to preexisting contents; ordinal refinement exists with distinct ordinals,
but is not a unique refinement. The device interface index is not a lifecycle stamp.
TX occurrences name whole batches, not unique constituent packet IDs.

Original enqueue gives peer capacity priority: ENOSPC emits no ring offer; EPIPE
emits refusal after possible peer-queue/packet changes; success independently requires
a resident non-full entry ring. Neither refusal is classified as packet disposal.
Queue-work Stop before installation emits no
admission. Consumption is emitted after branch check and installed replacement,
before later getters/decryption/checksum/publication can Stop. Softirq runs first;
padding precedes checksum; a failed encryption marks DEAD and publishes the saved
whole list after breaking. RX callbacks are concretely discharged; generic TX
checksum/softirq/rescheduling contracts remain explicit. Normal endpoint framing
alone is not failed-prefix event completeness; source cuts separately establish it.

Outer poll logs only its drop site, not callback-internal work. `RetainsRx` allows
deletion; actual later getters restore residency on normal paths. Offers record
successful completion bytes/skb/workDone before GRO; `none` (including keepalives)
emits nothing, and a refused second held offer remains pending, not an invented
drop. Callback entry is emitted before `deliverInner`, including a failing call,
without claiming visits to the remaining suffix. Selected normal-then-held order
holds within one poll, not across polls. Repeated skb IDs remain allowed; local
ordinals are neither allocation identities nor cross-poll uniqueness.

**Retired chronological claim.** Over `2c7a076`, `original_poll_callback_prefix` stated that callback
entries form a prefix of tagged successful completion buffers. Real GRO at `f45bde8` invalidates it. The
theorem is retired; `GroSafe` retains its original definition. The accepted chronological counterexample
remains valid.

**Accepted GRO counterexample.** `proof-campaign-replay.py r4-gro-reorder` constructs six operations
with explicit records. One batch receives nonce 0 carrying a one-byte ACK-only TCP segment (ports
40001→80), then nonce 1 carrying a SYN on a different flow (40002→443), under one peer/key allocation
lifetime. `DeliveryOrder/ReplayGro.lean` checks original `executeTrace trace false` acceptance,
identical checkpoint/acceptance-observer JSON, exact validator history `(lifetime, 0), (lifetime, 1)`,
and input ciphertexts against that lifetime’s receiving key. Output appends the SYN’s RST at outgoing
nonce 1, then the ACK’s RST at nonce 2; both byte-exact ciphertexts also occur in the original runner’s
final observable rows. Lifetime preservation, counters and receive-store cleanup are checked. This is
generated accepted mirror input, not a Linux capture or proof of kernel schedule reachability. The
audit-carry checkpoint is `3d50a4a`. Reproduce with:

```sh
capped -- scripts/in-bundle bash -o pipefail -c 'python3 -B docs/proof-campaign-replay.py r4-gro-reorder | lake env lean --run Leanux/Proofs/WG/DeliveryOrder/ReplayGro.lean'
```

The ACK remains GRO-held while the SYN enters the normal list; completion appends the held segment
behind it. `original_gro_held_then_normal` proves the original helper equation `napiGroReceive H;
napiGroReceive N; napiGroFlushAll = callback [N,H]` under the original classifier’s hold/normal
hypotheses. This is a design nuance at the post-GRO stack boundary; it does not show reversal of
WireGuard’s receive queue or decrypt FIFO. C supports these different-flow inputs (`tcp_offload.c:261,318,379–381`, `gro.h:528`,
`dev.c:6385,6388`). Two separate source concerns remain unconfirmed: zero-payload `len < mss` flushing,
and inspecting an existing same-flow held segment on the normal arm. Neither is a reported differential
finding.

Concrete stack framing includes IPv4 TCP replies through original transmit and
loopback, and UDP/IPv6 inbox changes. It yields per-poll entry-queue removal prefixes,
buffered subsequences and exact-byte callback origins with distinct local ordinals;
it does not assert completed delivery. The concrete RX scheduler preserves eager
getDev, erase-before-section, cryptAhead, suspension, ambiguity and budget Stops.
Non-decrypt lifted calls have no RX mutation cut by separate source inspection.
Copied trials retain first non-hidden Stop, discard returned Worlds/events and
certify only reached prefixes, without claiming every candidate ran.

The balanced `lookupSrc; peerPut` cut in original `consumeDataDone` needs no
initial liveness, trie validity or ownership premise. A normal `Some pid` lookup
derives a resident peer with positive old refcount, so immediate repayment cannot
take the deletion branch. `original_lookup_source_reference_restoration` retains
the actual lookup result and the complete semantic Kernel endpoint; the map's
internal representation is not equated. The corresponding destination-lookup
lemma covers immediate repayment, not a whole transmit call. Explicit projections
retain RX queues, NAPI flags and all three key slots. Bounded slot affiliation is
preserved only if it already holds; missing key slots are allowed. Existing mixed
observers give unconditional erasure and allocation-safe failure histories.
These are normal-return restoration and failed-prefix access claims, not total
repayment, a failed World, affiliation initialization or whole-callback protection.

The W7 joint observer emits queue installation after the peer write, publication
only after the head-state write, removal after the original two getters and setter,
and completion entry before `createDataDone`. Complete createData/txStep erasures
retain original results, Worlds and Stops on all inputs. Direct createData access
and ring projections are unconditional; the full-step access projection requires
entry `AllocationInv`, with intermediate obligations concretely discharged. This
transports existing reached-prefix access safety and ring refinement; it does not
turn either into packet conservation or provide a failed World.

On reaching its return continuation, EPIPE returns without entering direct
cleanup; publication can Stop before that boundary. The ENOSPC continuation enters
cleanup, and a reached
DEAD head skips completion and enters disposal. The disposal tail frees the list,
then releases its saved key and supplied peer; a later Stop keeps earlier release
observations. Its normal returned World preserves `sent`. Strict `peerGet` derives
positive old refcount and immediate repayment restores the semantic Kernel.
The new publication contract retains every full TX queue across CPU selection,
work-record consumption and the final non-deleting put, even when enqueue and
keypair-derived publication peers differ. Normal EPIPE createData retains the
explicit caller's newly enqueued list, marks its actual first packet DEAD and
leaves the physical encrypt ring unchanged. Normal ENOSPC cleanup removes every
supplied packet slot; it does not promise preservation of an older peer queue,
since its supplied peer put may release that peer on arbitrary Worlds.

Normal list disposal erases exactly the listed TX records and retains other slots,
without allocation-validity or distinct-ID premises. A duplicate can Stop at its
second missing getter; the existing joint observer retains the earlier release
prefix, not a final World. At an actual txStep entry whose logical queue head names
a DEAD packet, normal execution returns true, frees the whole item and retains
`World.sent`. Both original head reads and drop getters remain in order. This does
not identify that entry with an earlier refusal across arbitrary intervening work.
Empty/malformed batches and missing peers/keys preserve their original Stops.

**Remaining obligations.** RX carrier preservation through relevant transmit
callbacks, enclosing ingress/runner/lifecycle, worker-local ownership and joint
receive-pipeline conservation remain open. Packet stores, decrypt rings, peer
queues, worker locals and GRO buffers contain overlapping references; their sizes
cannot simply be added. Initialized index/keypair affiliation, allocation/lifecycle
identity and named source dispositions require source-derived invariants. These
include early rejection, failed validation, keepalive consumption and purge/free
paths; a free after a GRO offer need not be a drop. The local W7 endpoint obligations
are checked; initialized source-item/mark transport between refusal and a later
DEAD worker entry remains open. Raw packet aliases can change that mark in between,
so no arbitrary-schedule linkage follows from the two local contracts.

A finite prefix must retain pending obligations. At an accepted drained boundary,
queue checks alone do not establish empty packet stores or peer queues. Stack
callback entry, normal completion and packet disposal remain distinct observations;
local poll ordinals do not establish cross-poll uniqueness. Universal outgoing
staged-to-socket conservation is not claimed or required by this receive result.

**Effort.** Counts are per slice; no memory cap was hit.

| Slice | Collected outcomes | Elapsed |
| --- | --- | --- |
| Before general geometry | 105 calls: 36 passes, 68 ordinary failures, one deliberate termination | Separate local slices |
| General geometry | 13: four passes, nine ordinary failures | 7m42s |
| Finite journals | 12 builds: four passes/eight failures; one passing scoped check | 11m11s validation; 12m02s ownership |
| RX source journals | Eight builds: two passes/six failures; scoped checks one pass/one failure | 19m07s validation; 21m45s ownership |
| TX source journals | Eight builds: four passes/four failures | 11m58s validation; 13m44s ownership |
| Concrete RX scheduler | 15 builds: four passes/eleven ordinary failures | 30m07s |
| Balanced lookup/reference cut | 15 builds: six passes/nine ordinary failures; one passing scoped check | 18m19s from first worker clock (08:55:24) through final full-target collection (09:13:43); 20m44s through token return; scoped/full targets 232/342 and coordinated validation pass |
| W7 joint observer/source cuts | 28 builds: six passes/22 ordinary failures; one passing scoped check; scoped/full targets 239/355 | 36m41s from grant 10:24:22 through full-target collection 11:01:03; 39m08s through token return 11:03:30; independent frozen review and coordinated validation pass |
| W7 normal endpoints | 21 calls: 20 builds (four passes/16 ordinary failures) plus a passing scoped check; scoped/full targets 243/365 | 20m51s from grant 12:09:19 through measured full-result collection 12:30:10; 23m18s total token ownership through handback 12:32:37. No cap/interruption, all exits collected. Independent frozen review and coordinated gate, fresh kernel replay, default build and 114 unit tests pass. |

Failures were elaboration/replay assertions; the RX scoped check rejected the
English token “admit” and passed after correction. Scheduler integration exposed a
duplicate Activation matcher, resolved with canonical frames and legacy projections.
The balanced-reference tranche encountered record-layout/getter normalization
failures and a duplicate peerPut matcher. Normalizing the known Option alone did
not fix the latter; sharing the existing WGBase proof environment did.
The W7 tranche replaced repeated broad source normalization after a deterministic
heartbeat failure with explicit exact source-tail factors. Other failures were
ordinary elaboration, loop/match normalization and projection-wrapper issues;
no cap, process termination or interruption occurred in this tranche.
The endpoint extension used a queue/refcount projection and exact packet-store
frames; ordinary failures included tactic syntax, function-equality instantiation,
Option/match reduction and source/postcondition composition. No endpoint behavior
was supplied as a premise. Review fixed the effort-table row formatting and added
the explicit normal-return and source-entry conditions to the claim table. Frozen
Lean review has no unresolved finding.
Review qualified EPIPE at its reached return continuation because publication may
Stop first, and corrected the source-declaration census separately from the preceding
coordinated-validation counts. Both documentation findings are fixed.
A completion-frame worker had two implementation interruptions and one reporting
interruption; dirty worktrees were preserved. Separately, the initial ring writer
resumed after deliberate termination without the required snapshot. Work stopped;
the coordinator preserved all six dirty worktrees before resumption. Symbolic slot
algebra replaced the large reduction. This process failure is not an ordinary
compile failure. Reviews fixed callback-log scope, required direct correspondence/
provenance, replaced “unique refinement” by existence with distinct ordinals,
“epoch” by interface index, and “ownership” by contents; they also corrected
normal-endpoint/Stop, positive-size, copied-frame/header and table/status wording.
The balanced-reference review corrected a terminal's suggestion that the immediate
positive-count repayment consumed hidden records; its branches append steps only.
It also replaced inherited device-epoch wording in the map and queue-view header
with interface-index wording; the existing field and API names remain unchanged.
The subsequent scope review distinguished EPIPE's DEAD publication and later
worker disposal from ENOSPC's direct cleanup in the remaining W7 obligations.

**Ranked mirror suggestions.** None. Physical occupancy/batched retirement explain
W7, and proof-side frames/projections handle local polling without production changes.

## R5 — key lifetime enforcement: Rule Zero findings

**Original versus proved.** Unconditional encryption-age/post-zero claims are false
in accepted mirror inputs; RX authenticates before wire-nonce validation. Rule Zero
resolves those statements, retaining thirteen [local contracts](../Leanux/Proofs/WG/KeyLifetime/Statements.lean).
Universal transport of TX certificates and whole-run AEAD coverage remain unproved.

| Original wording | Checked result and reason |
| --- | --- |
| No encryption/decryption under a key older than `REJECT_AFTER_TIME` | RX attempts require the actual unexpired recorded comparison. TX checks age at staging; an admitted keepalive can encrypt after later recorded expiry. |
| No use past `REJECT_AFTER_MESSAGES` | RX checks stored counter before AEAD and wire nonce afterward; R/R+1 authenticate before rejection. This refutes the wire-nonce reading, not the stored-counter guard. TX assigned nonces are certified below R. |
| No key-material use after zero timer until a new handshake | The timer queues clear work; even after published slots/index are cleared, a queued packet reference retains material until encryption/transmission releases it. |

Time witnesses are **type-4 transport keepalives with empty plaintext**, not nonempty
inner IP packets. Generated accepted inputs are not Linux captures or demonstrated
kernel schedules. Linux `receive.c:242–331`, `send.c:162–219,342–414`, `noise.c:112–177`
and `timers.c:105–133` explain authentication-before-validation, TX admission checks
and refcounted clearance. These are charter statement artefacts, not demonstrated
Linux security defects; no upstream-tray entry is justified by this evidence.

| Model | Abstraction and refinement |
| --- | --- |
| `KeyTimes/Clock` | Exact `original_age_test`/`original_age_branch`, wrapped signed64 deadlines, consumed clocks and operands; equality is expired. |
| `Receive`, `ReceiveAttempts` | Original source factor derives validity/stored-counter/unexpired admission; events immediately precede actual AEAD after guards/allocation/fragment checks. Exact erasure, singleton coverage and failed-authentication endpoint prevent empty-log vacuity; later validator acceptance bounds the wire nonce without bitmap-shape premises. |
| `Staging` | `original_staging_erasure`/`original_staging_admissions` certifies actual key/clock/allocation executions and bounded nonce arguments just before `createData`, retaining certificates after later Stop; it does not prove subsequent immutable material transport. |
| `ZeroTimer`, `Logged/TimerPass`, `Logged/Advance` | Complete transport-store frame and exact unit/whole-advance erasures, retaining descriptor/seccomp/task-work effects. Crypt observations are scheduler calls, not per-packet AEAD events. |

[AGENT 2026-10-13] Resolve the false original statement through accepted Rule Zero
counterexamples; keep positive contracts at their proved boundaries and stronger
transport theorems as follow-on work. Distinguish generated clock arithmetic from
measured kernel execution.

**Counter witnesses.** `r5-rx-wire-limit` reconstructs the tracked five-operation
session and authenticated nonce-R packet. `r5-rx-wire-past-limit` derives the session
with the harness Noise helper, matches the tracked response and generates nonce R+1,
where `R = 18446744073709543486`. Original/observed JSON agrees: stored-counter operands
are `[0,R]`, AEAD succeeds, then validation rejects `[R,R]` or `[R+1,R]` with empty
acceptance history. This is authenticated decryption followed by drop, not delivery.

**Delayed encryption.** `r5-delayed-encryption` creates a session at 132s and uses two
nonempty receives to set the keepalive second-fire flag. Nonce 1 is admitted at 311s
with age operands `[312000000000,311000000000]`. At 322s the next callback records
`[312000000000,322000000000]`, invalidates sending, stages another keepalive and queues
a handshake. Crypt encrypts/transmits the earlier packet with unchanged material
before that handshake. Original unit order, packet/key identity, refs and ciphertext
arrival are asserted, not inferred from a scheduler observation alone.

**Post-clear use.** The seven-operation `r5-coherent-post-clear` moves the second
expiry comparison to 673s. Zero expiry is 132+540=672s; zero and actual clear work run
before crypt. All three published slots are empty, index absent and handshake zero,
but the same packet retains exactly one reference to the same material. New ciphertext
appears before queued handshake work; transmission frees packet and final key reference.
The older five-operation `r5-post-clear-transport` deliberately uses incoherent
coarse/jiffies clocks and disabled arm records; the new case does not upgrade it.

Both coherent variants enable arm records and check monotone coarse-nanoseconds/
UInt64-jiffies, exact delays and `J(t) = 2^32 - 75000 + 250*t`; site128/kind310 windows
end at 323/674s. Queue/timer identities are stable and TAI advances by elapsed coarse
time; cache-clock records remain disabled. The timer-window rule permits late callbacks.
Each observer starts at an accepted checkpoint with the next operation's records;
complete original advance equality checks Kernel, decisions, receiving endpoint,
jiffies and record exhaustion, plus retained material/new exact ciphertext.
Arithmetic coherence does not establish Linux scheduling reachability.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r5-rx-wire-limit |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/Replay.lean
python3 -B docs/proof-campaign-replay.py r5-rx-wire-past-limit |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/Replay.lean
python3 -B docs/proof-campaign-replay.py r5-delayed-encryption |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/ReplayDelayed.lean
python3 -B docs/proof-campaign-replay.py r5-coherent-post-clear |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/ReplayDelayed.lean
python3 -B docs/proof-campaign-replay.py r5-post-clear-transport |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/KeyLifetime/ReplayPostClear.lean
```

**Review disposition.** The [independent review](2026-10-13-review-r5-counterexamples.md)
of `7fc444d` agrees on classification/local statements; its clock qualification is
in the [timer-model note](2026-10-13-review-items-7-8.md#proof-domain-qualification).
The reviewed uncommitted witnesses landed in `3d50a4a`; all five recipes passed the
audit carry. We do not adopt two supporting assertions: authenticate-then-check is
actual, not logically necessary (numeric nonce rejection could precede replay update),
and these witnesses establish no measured/universal Linux worker-latency bound.
Kernel reachability is unestablished, not impossible. Rejection preserves receiving
counter/non-delivery, not the whole World. The proposed 128-packet per-staging bound
is false: C `device.c:207–217` trims old contents before adding excess GSO segments;
1024 crypt-ring slots count batches, not globally retained packets. Three terminals
are erasures (staging/timer pass/receive attempt), correcting the review's count of two.

**Effort.** Receive/time: 17 builds, ten ordinary failures; staging: ten/six;
RX attempts: four/one; timer observer: four/two. Thirteen replays had eight passes,
two Lean-syntax failures and three generated-record/jitter failures; all five final
recipes passed in under nine seconds each. A gate rejected “admit” in a diagnostic
string and passed after correction. One provider interruption left no job running;
all dirty worktrees were preserved before edits resumed. No cap was hit; reviewed
assertion/source/scope corrections are resolved. No new guest execution is claimed.

**Ranked mirror suggestions.** None required. Signed clock helpers and operand
records expose the semantics. Adding a later encryption-age guard would change C
control flow and is not altitude-preserving.

## R6 — cookie exclusion and retry-limit finding

**Lifecycle source discrepancy at `c047e64` (not yet a replay finding).**
`Receive.ratelimiterAllow` now creates and updates IPv6 entries in `table6`,
but `Device.ratelimiterInit` resets only `table`, and `gcEntries false` walks
and clears only that IPv4 table while reporting no IPv6 entries. The local
Linux `ratelimiter.c:55–83` walks both families and clears every entry on the
last uninit (`:205–221`); reinitialization allocates empty tables. Thus the
mirror source appears to retain IPv6 rate-limit state across the last uninit
and reinit. This was found while preparing R2 lifecycle composition and checked
against both sources. No accepted runner reproduction or differential result
has yet been established. It is not a Linux bug claim or a premise of the
cookie-exclusion theorem, and the campaign has not edited the mirror. A
follow-up should exercise IPv6 cookie admission, device deletion/recreation
and admission from the same source /64.

**Original versus proved.** Under-load invalid-MAC2 exclusion has an original
cookie-only source theorem and complete Noise frame on normal completion. Literal
`MAX_TIMER_HANDSHAKES` attempts is false: the accepted episode has 19 retries/20 total
initiations with MAX=18. C's strict `attempts > MAX` and `timers.c:49`'s MAX+2 report
explain this design/wording nuance, not a mirror/C disagreement.

**Architecture/refinement.** [Six terminals](../Leanux/Proofs/WG/FloodResistance/Statements.lean)
connect `Cookies/Gate`'s exact original `receiveHandshakePacket` factor to
`original_invalid_mac2_cookie_only`/`original_invalid_mac2_noise_preserved` and the invalid-MAC1 drop.
`FailedMac2` contains actual load and `makeCookie` executions, MAC1 equality and
MAC2 inequality against that invocation's returned cookie. Derived `noCookie` plus
seven original branch records reaches only the reply suffix; exact equality retains
reply Stops. Invalid MAC1 takes the five-record drop before cookie creation/Noise.
`Cookies/Load` derives active load from queue depth≥512 or actual unexpired signed
recorded decay. `Cookies/Frames` masks only cookie secret/birthdate and TX packet/byte
stats from the complete Device, retaining global peer/keypair counters, full resident
records, static identity, indices/frontiers and all other fields. Both cookie calls
may rotate; both families, allocation refusal and ordinary socket errors are covered.
Missing records can Stop. This is one original call, not outer workers/scheduling;
valid-MAC2 rate limiting is a separate path.

**Accepted retry episode.** `r6-retransmit-limit` derives 23 operations from tracked
`d3_retransmit_gives_up` and initiation draws, with explicit coherent coarse/jiffies/
arm records, advancing TAI and disabled cache clocks. Original runner acceptance,
checkpoint JSON equality, stable peer identity, empty key store, timer/counter/queue
boundaries and new initiation bytes are checked. Callbacks 1–19 increment and queue
send work; each sends/rearms. Callback20 compares `[19,18]`, gives up without sending,
purges staging and arms deferred zero; callback19 compared `[18,18]` and rearmed.
Generated accepted input is not a capture/kernel scheduling proof. This episode
implies no universal bound through reset/rate/dead/allocation/socket alternatives.

`Logged/Advance` and `original_advance_observer_erasure` retain the complete original
advance syscall's seccomp/dispatch/task-work prefix, result, successful World and Stop.
Recorded units are observed; the lifted placeholder path has no unit-coverage claim.
The same interface connects the two coherent R5 time witnesses.

```sh
set -o pipefail
python3 -B docs/proof-campaign-replay.py r6-retransmit-limit |
  capped -- scripts/in-bundle lake env lean --run Leanux/Proofs/WG/FloodResistance/Replay.lean
```

[AGENT 2026-10-13] State cookie exclusion over actual rejection executions and retain
the literal retry counterexample. Do not replace it with an unproved universal
episode bound or promote generated records to measured kernel schedules.

**Effort/review.** Cookie proofs: thirteen builds, three passes/ten ordinary failures;
the abstract load-continuation factor avoided broad expansion without weakening the
view. Retry/Advance: nine calls, five passes/four compile/assertion failures, including
a corrected reply-endpoint assertion. Final retry and strengthened R5 time checks pass.
All exits were collected without cap/interruption; source/contract review and its
two reporting corrections are resolved. `66df779` records the review/tray carry.

**Ranked mirror suggestions.** None for these properties: source factors and the
existing boundaries suffice. Changing retry comparison would alter C behavior and
is not altitude-preserving; it is not proposed. The lifecycle discrepancy above
requires its separate reproduction/validation, not a proof-driven mirror edit.
