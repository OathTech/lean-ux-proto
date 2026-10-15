# WireGuard proof campaign

## Progress

Work is on `.worktrees/proofs-campaign`, branch `proofs/campaign`, under
[the charter](2026-10-13-charter-proof-campaign.md). The mirror remains byte-identical
to `ca6b22e`. The current R4 environment-caller extension passes coordinated validation
and independent frozen review.
The [proof register](proofs.md#results) holds current declarations and
pins; its [model map](proofs.md#layers) supplies the complete module inventory.
Current components are not completion of the open charter properties. This campaign
has made no main integration, push, differential check or guest run.
[AGENT 2026-10-14] Keep the module inventory/register in the proof map; this report
retains current architecture, findings, reproduction provenance, effort and limits.

| Result | Current disposition |
| --- | --- |
| R1 | Uniqueness and the intentional inclusive-floor correction are proved, with pure and accepted-run witnesses. |
| R2 | Initialized allocation-identity access safety now holds for every typed Runner trace and both placeholder/flood modes, including failed histories. Every reached consistency-filter entry derives its own allocation invariant and safe isolated trials with exact ordered filter correspondence. No parser, array-length, progress or success premise is added. Raw-reference affiliation/credit remains a separate stronger property. Coordinated validation of the three new exports passes. |
| R3 | Initialized finite normal call histories refine flat-prefix updates and reached-root lookup, including full normal clear. Completed setAllowedip/removal events now cover the complete public peer command, with source-derived acquisition and concrete send/flush/cleanup frames. Successful public parseTrace supplies every configured peer's address shape. The complete original device command now composes clear/removal/peer-command completions; normal clear/remove-all leaves the folded tables empty. Optional routing now includes absent devices, guarded creation, down, destruction/deletion and all fixture/prefill modes. Whole absent peer/device commands retain their entry journals, without assuming interface lookup failure. Concrete silent TX/Stack/RX completion and poll now retain routing and surviving lists, with explicit frames for generic worker callbacks. Concrete receive admission, both direct NAPI poll callers, IRQ placement, crypt iterations, five timer callbacks and device open/up/namespace exit now close further original callers. Session helpers, incoming Noise/cookie processing, complete handshake receive and the actual receive-worker iteration now have concrete routing frames too. Whole-call lifts leave completion histories unchanged. Enclosing scheduler/Env/syscall/Runner execution and packet paths remain open. |
| R4 | Physical rings, finite/source journals, selected GRO order and concrete RX scheduling are checked. A joint stamped poll proves full callback/removal provenance, per-poll stamp uniqueness on every prefix and observed release on normal return, from valid prior lifetime history. Accepted input refutes chronological post-GRO order. Capture reads now support removal and entry stamps in the new suffix, excluding prior releases. Finite original-poll sequences compose distinct entry stamps with a direct audit projection. Both direct poll sites and the IRQ-exit wrapper now preserve this boundary with exact original erasure and direct R2 audit projection. Concrete crypt-worker iterations, transmit pre-encryption and one activation iteration now observe their reached NAPI callbacks with the same direct R2 audit projection and boundary contracts. Complete activation runs, dispatch, recorded scheduling and nested rescheduling now compose stamped committed polls with exact full-audit projection and actual filter probes; copied trials remain isolated. Deferred crypt/send continuations, injection, both flood receive-worker modes and batch items/full submission now retain actual scheduler calls and NET_RX inline polling with the same direct audit and boundary contracts. Enclosing timers/observation/lifecycle and initialized Env/Runner coverage plus joint pipeline conservation remain open. |
| R5 | The unconditional age/post-zero and wire-nonce readings are false in accepted mirror inputs. Rule Zero resolution retains thirteen positive local contracts, without universal replacement transport claims. |
| R6 | Cookie exclusion is proved at its original call boundary. A 19-retry/20-initiation episode refutes literal MAX=18; no universal corrected retry bound is claimed. |

**Validation status.** The R4 environment-caller extension passes its 293-job
scoped Statements and 458-job full proof builds. The gate passes all 464 terminal
declarations (105 R4; 462 theorems and two definitions) with permitted axioms only.
Fresh stock kernel replay, the 60-job default build and 124 unit tests
(23.730 seconds, one skip) pass. Exact six-file scope/hashes, all 460 prior
terminal statements/proof bodies, census, tokens/imports, whitespace including
new files and mirror equality pass. Independent frozen review is clear after
correcting the secondary R4 claim-boundary row. The replay, default build and
units ran concurrently with unchanged caps; no rerun. No runtime source or
reproduction has changed.

[AGENT 2026-10-14] Condense repeated checkpoint validation here; the
checkpoint commit messages retain historical counts and timings, and the result
effort tables below retain failed attempts and their disposition.

[AGENT 2026-10-14] Use command-scoped Codex author and committer settings for
local checkpoints. Checkpoint `e7b0273` mistakenly inherited the default Git
identity; subsequent commits correct the attribution without changing global
configuration or rewriting the active branch's ancestry.

**Lean 4.35 carry (`ca6b22e`).** Five proof-file repairs changed type inference
and generated-VC tactics, preserving all 417 terminal statements at that
checkpoint. Gate, fresh replay, default/executable builds and units passed;
eleven reproductions gave nine accepted original/observer agreements and two
expected pending-dump rejections. Historical counts and timings are in commit
`b1ec9e8`; later declarations use the current validation above.

A supplementary explicit export of all 417 terminal declarations and their
dependencies passes Lean paranoid, lean4lean, nanoda, con-leche, con-ron and Lean
default; its axiom report contains only `propext`, `Quot.sound` and
`Classical.choice`. This export-only run uses `--inadvisably-no-sandbox`, so it is
a speedbump, not a sandboxed project check. A plain `lake check` would cover the
default targets, which exclude `LeanuxProofs`. The first attempt failed before
checking because the bundle PATH omitted `git`; one infrastructure retry appended
`/usr/bin` only in that command's environment and passed within its 900-second
bound (19:44:08 to result collection at 19:50:45 UTC). No global state changed.
At that checkpoint, initialized whole-run R2 and remaining R3/R4 closures remained open.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle scripts/proof-gate
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs
LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build
LEAN_NUM_THREADS=32 capped -- scripts/in-bundle lake build leanux-model
LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle python3 -B -m unittest evaluator.test_evaluation evaluator.test_model_replay harness.test_trace harness.test_wg harness.test_linux
```

To repeat the supplementary export check, in this checkout:

```sh
mkdir -p .tmp
capped -- scripts/in-bundle lake env python3 - <<'PYEXPORT'
from pathlib import Path
import runpy, subprocess
names = runpy.run_path("scripts/proof-gate", run_name="proof_gate_names")["terminal_statements"]()
with Path(".tmp/campaign-proof-export.ndjson").open("wb") as output:
    subprocess.run(["leanexport", "Leanux.Proofs", "--", *names], stdout=output, check=True)
PYEXPORT
capped -- timeout --signal=TERM --kill-after=10s 900s scripts/in-bundle sh -c 'PATH="$PATH:/usr/bin"; export PATH; exec lake check --from-export=.tmp/campaign-proof-export.ndjson --paranoid --inadvisably-no-sandbox'
rm .tmp/campaign-proof-export.ndjson
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

The `ca6b22e` / Lean 4.35 carry mirrors the original dump walk's explicit
`List PeerId` annotation in both its source factor and lifetime observer.
The pipe frame selects its continuation by goal type, while ECN encapsulation
and fdtable allocation compose existing complete-Kernel frames instead of
expanding nested World-valued automatic VCs. Five proof files change; all
417 terminal declarations, legacy APIs and reproduction recipes are retained.
Toolchain deprecation warnings remain visible; no tactic-limit or global-setting
change is used.

| Carry | Measured effort |
| --- | --- |
| Seccomp/shared frames | 17 compile passes; 36m34s. |
| Prerequisites `2c7a076` | About 40m, 12 local builds; earlier transmit/stack work five attempts. |
| Audit `f45bde8` | 14 root, six R2 and sixteen R4 build/probe calls before passing gates and nine replays. |
| Scheduler `7a92672` | 15 calls: 14 passes, one failure; 16m20s validation, 17m22s token ownership. |
| `c047e64` | 23 calls: 14 passes, nine ordinary failures (seven proofs, two replay parsers); 29m33s. |
| `43c7549` | Two capped builds, both PASS (148-job scoped closure, 321.28s; 401-job full proof closure, 298.03s); zero ordinary failures, cap kills or interruptions. All exits collected; one cheap uncapped scope/census check passed; the coordinator repeated it under capped, passing exact ten-file scope, eight frozen Lean hashes, 403 declarations, whitespace and mirror equality. 12m50s from grant 16:47:30 through full-result collection 17:00:20 UTC. Eight Lean files; independent frozen source/documentation review is clear after the status-wording correction, and sequential coordinated proof gate, fresh kernel replay, default/executable builds, 124 unit tests and eleven reproductions pass. Token returned at 17:03:32 (16m02s ownership). Recipes are unchanged. |
| `ca6b22e` / Lean 4.35 | Eight capped calls: six builds (three PASS: 147-job scoped, 182-job scoped, 420-job full; three ordinary FAIL) plus two passing exact scope/compatibility checks. Failures were automatic VC recursion in ECN encapsulation, one incomplete structural tactic attempt, and the first full build's fdtable VC recursion plus dump-observer collection inference. That failed collection elaboration also emitted recovery `declaration uses sorry` diagnostics; no source admission was introduced. The corrected full build and final axiom gate pass without non-standard axioms. All exits collected; no cap kills or interruptions. Grant 19:14:43, full result collected 19:32:55 UTC: 18m12s. Five Lean files and two docs; all 417 terminal declarations and 240 changed-module declaration headers are unchanged. Independent frozen review is clear; the historical-pin wording correction is retained. Sequential coordinated gate, fresh kernel replay, default/executable builds, unit tests, eleven reproductions and exact frozen checks pass. The supplementary export-only six-checker run also passes, with the sandbox and one infrastructure retry limits stated above. Token returned 19:37:12 UTC (22m29s ownership). |

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

## R2 — lifetime identity and retained references

**Original versus proved.** The charter requires that no later access resolves
an identity released earlier. Initialized whole-run allocation-identity access
safety now follows for every typed Trace and both placeholder/flood modes,
including failure prefixes. No parser, hidden-array length, progress, successful
execution or initial-invariant premise appears in the three Runner exports.
Raw-reference affiliation and credit accounting remain stronger separate
properties. Historical stale-cursor findings retarget a replacement identity;
they do not resurrect the released identity.

**Architecture/refinement.** [Terminal contracts](../Leanux/Proofs/WG/LifetimeSafety/Statements.lean)
retain exact original results and indexed Stops. Concrete syscall contracts,
original fixture initialization and successful prefill discharge the local
invariant premises in the initialized theorem. A failed execution retains its
history, not a final World. Unchanged endpoints or erasure alone do not prove
access coverage; the literal observers and lifted helpers are separately
inspected against source.

| Model | Abstraction and refinement boundary |
| --- | --- |
| `Lifetimes/Store`, `Actions`, `Keypairs/Identity` | Slot/allocation stamps and original-execution transitions; `keypair_syscall_no_resurrection` and peer/packet sequence contracts. Packet primitive results are within one device epoch. |
| `Logged/Prefix`, `Focus`, `LifetimeEvent.Safe` | Mixed access/release histories outside the exception layer; packet stamps are `(ifindex, id + 1)`. All-input erasure and safe reached prefixes. A failed getter resolves no object and emits no access. |
| `ReleaseInv`, `AllocationInv` | Resident uniqueness, current slot/lifetime frontiers and past packet-epoch bounds; `allocation_initial_fixture` and concrete preservation establish allocator vacancy. Arbitrary occupied-slot behavior remains in erasure, not in a safety conclusion. |
| Ambient contracts and canonical Kernel projections | Preserve chosen invariants through source-shaped leaves; legacy interfaces project shared frames. Queue scalar preservation does not establish reference credits. |
| `SavedPeers`, prefix loops/workers | Observe demanded captured entries, including predicate misses, with saved-stamp residency obligations; exact bounded-loop erasure retains callback/exhaustion Stops. |
| `BatchTrials`, `BatchCalls` | `scheduler_family_access_erasure`, `scheduler_family_allocation_access` and `scheduler_trial_filter_access` separate committed calls from copied-World trials. The ordered filter propagates its first non-hidden Stop; each reached trial has an isolated safe prefix from the same entry invariant. |
| `Audit`, `BatchAudit` | [AGENT 2026-10-14] Carry saved consistency-filter entry facts in `AuditM` through remaining callers, avoiding separate reachability threading while retaining failed histories and separate trials. The sum event stream projects to committed lifetime events and records the actual current World/projected history immediately before each original filter, including empty filters and Stops. `AuditInv` combines current `AllocationInv` with validity of every saved entry. Result-dependent focus preserves cached predicates and old probe facts. Literal scheduler/nested-reschedule/receive-worker observers have unconditional source erasure, allocation-conditional committed projection and concrete failed-prefix safety. Empty-history local allocation validity derives safe trials at every recorded entry; exact filter correspondence preserves order and early failure without asserting unevaluated candidates ran. The literal source placement and exact filter-entry equation supply coverage; projection alone does not. |
| Deferred environment workers and timers | [AGENT 2026-10-14] Reuse Audit composition for actual scheduling and focused local lifetime calls; share captured-map optional lookups so each present peer-list occurrence emits its saved-identity read and missing entries emit none. Complete scans precede callback effects; original short circuits, section records, timer detachment, finite bounds and failures remain exact. Full-Kernel bookkeeping frames project legacy APIs, and literal timer source cuts share the original pure scan/fold. Fifteen typed calls have unconditional erasure, concrete AuditInv prefix safety and reached-trial facts from local allocation-valid entries; initialized entry is discharged by RunnerSafety. |
| Remaining environment callers | [AGENT 2026-10-14] Share source-only observation and per-item batch cuts, while keeping concrete Audit observers at actual device, receive, multicast and inline-poll calls. Full-Kernel leaves and an MTU/inet scalar mask retain residents/frontiers; flood queue updates preserve identity and metadata while allowing byte/source queue changes. Both flood modes keep audit-aware nested receive callbacks; complete saved-map scans, partial CQEs, delete guards, finite budgets and failed histories remain exact. Fifteen typed calls have unconditional erasure and concrete local AuditInv/reached-trial contracts; initialized entry is discharged by RunnerSafety. |
| Complete syscall callers | Literal callback-parametric socket/netlink/rtnetlink observers preserve source cleanup only on ordinary returns, including negative results. Shared full-WG framing covers the four holder closes/taskWorkRun; actual namespace cleanup remains in the postworker suffix. All 34 typed constructors/35 dispatch arms retain exact descriptor/route/MTU/dump guards, observation-before-fdcheck, source resets and seccomp/postworker order. Three grouped contracts give unconditional erasure, concrete AuditInv failed-prefix preservation and reached-trial facts from local entry AllocationInv. Arbitrary typed arguments need no parser-validity premise; initialized entry is discharged by RunnerSafety. |
| `PrefixOuter`, `RunnerAudit`, `RunnerSafety` | History is outside indexed exceptions. The literal Runner retains initialization, seccomp prefill, defaulted hidden-array lookup, syscall/ambient order, all five postchecks, output loops and exact JSON. Explicit success and exception WP postconditions retain AuditSafe; the operation-loop invariant carries AuditInv on its actual World. Original fixture/prefill and concrete syscall/ambient contracts discharge every helper premise. Reached markers supply their saved World/history to exact ordered filters and isolated trial safety; unevaluated candidates are not claimed to have run. |
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
preserves every source-coverage obligation; the initialized Runner theorem now supplies this composition.

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

**Scope and remaining properties.** The initialized Runner composition closes
the stated allocation-identity access property. `BatchTrials` retains its useful
conditional local contract; the initialized audit now derives that condition at
every actual reached filter entry. Activation.run uses plain condResched and
has no nested consistency trial; flood/receive-worker callers carry audit-aware
nested rescheduling. Actual queued namespace cleanup runs at the original
postworker cut. Failed histories remain safe without asserting a failed World.
Raw-reference affiliation and credits remain separate: a stale scalar reference
may resolve a fresh replacement identity or Stop. R3 routing and R4 conservation
are not consequences of this access theorem. C initializes cache/handshake before
incrementing the peer counter; the mirror increments/inserts first. The theorem
follows the mirror and is not a C simulation or physical-memory-safety claim.

The original `trace.hidden.map (·[index]!)` is retained for arbitrary typed traces.
Lean's pure defaulted lookup semantics supplies `[]` outside array bounds; no
parser-validity premise is added. Exact erasure concerns JSON and indexed Stops,
not executable diagnostic output from a defaulted lookup.

[AGENT 2026-10-14] Reuse the established Logged.Runner local 2,000,000-heartbeat
setting for the new Runner modules after the default 200,000-heartbeat erasure
attempt failed. This preserves the existing proof architecture; capped process
limits and global settings are unchanged. Explicit exception-history WP branches
and the established ordinary mvcgen loop rules close safety; enabling join-point
sharing initially left additional continuation predicates unresolved.

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
| Initialized Runner | 16 capped calls: 13 builds (6 PASS / 7 ordinary FAIL) plus three checks (2 PASS / 1 ordinary FAIL) | First full result at 20:02:50 UTC, 10m18s from grant 19:52:32; final full result after comment corrections at 20:07:54, 15m22s. Foundation/observer/safety/terminal/full targets 33/242/243/280/423; three new exports, 208 R2 / 420 declarations. Four initial failures concerned generic transformer reduction/type inference, one hit the default erasure heartbeat limit, and two concerned WP continuation/prefill/reset elaboration. No source-contract gap, changed premise, cap kill, interruption, recovery admission diagnostic or runtime replay; all exits collected. Call 14 passes exact six-file scope/census/whitespace/mirror and compatibility: all 417 prior declaration statements/proof bodies are unchanged, with stale local-scope comments corrected. Check 15 failed only because a prose substring assertion did not allow a line break; removing that unnecessary formatting assertion gives passing check 16. The final check confirms all four frozen Lean hashes and the current source census/scope; this ledger count is the subsequent documentation-only delta. Independent frozen export/documentation and bounded source-coverage reviews are clear, with stale-comment findings corrected. Sequential coordinated proof gate, fresh stock kernel replay, default build and 124 unit tests pass; the capped exact check confirms all four frozen Lean hashes. Token returned at 20:13:04 UTC (20m32s ownership). |

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
original calls, plus complete peer/device-command completion prefixes and public
parser address shape. Optional routing now handles absent devices and actual guarded
creation, down, destruction/deletion, plus all initial fixture and successful prefill
modes. Enclosing syscall/Runner execution and the packet claim remain open.
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
| `PeerCommandCompletion`, `ParserShape` | Literal public preflight/acquisition suffix, derived optional-peer residency and complete command prefixes; actual private parsePeer/config/operation plus the pause-stripping accumulator and exact public-parser suffix derive every configured peer's address shape. `original_setPeerCmd_completion_erasure`, `original_setPeerCmd_routing_prefix`, `parsed_trace_peer_commands_routing`. |
| `RoutingDeviceFrames`, `DeviceCompletion`, completed clear/remove-all | Strong configuration/socket projections and concrete cache/key-expiry frames; all four original DeviceSource cuts compose actual clear/removal/peer-command events. Normal clear/remove-all leaves folded flat tables empty, without physical-node emptiness or totality. `original_device_configuration_completion_erasure`, `original_device_configuration_routing_prefix`, `parsed_trace_device_configuration_routing`. |
| `RoutingGlobal`, `RoutingDeviceLifecycleFrames`, `LifecycleCompletion` | Absence denotes empty flat tables; present states retain the existing invariant and event validity. Original guarded create/down/destruct/delete and absent whole configuration paths preserve safe completion prefixes. Actual fixture/prefill initialization includes bare and nonnetwork modes. `original_optional_lifecycle_erasure`, `original_optional_lifecycle_routing_prefix`, `original_optional_routing_initialization`. |
| `RoutingTxFrames`, `RoutingRxFrames` | Original TX entry/completion/worker, concrete Stack and RX completion/poll retain routing tables/frontiers and surviving peer lists; release may delete residents. Generic worker/GRO callbacks have explicit frames, with actual checksum/Stack discharge. Whole-call lifts erase exactly, preserve optional completion state on normal return and leave the journal unchanged on every outcome; Stop retains prior history safety without a returned World. `original_tx_routing_frames`, `original_rx_routing_frames`, `original_traffic_routing_completion`. |
| `RoutingAdmissionFrames`, `RoutingNapiFrames`, `RoutingMaintenanceFrames` | Actual receive admission, both direct poll callers and IRQ placement, concrete crypt iterations, five timer callbacks and device open/up/namespace exit retain routing and surviving lists. Original negative cleanup and Stops remain; no residency, affiliation, credit, saved-list or drain premise. `original_receive_admission_routing`, `original_concrete_napi_routing`, `original_timer_device_routing`. |
| `RoutingSessionFrames`, `RoutingNoiseReceiveFrames`, `RoutingHandshakeReceiveFrames` | Original session helpers preserve the routing view; incoming Noise/cookie and complete handshake receive permit peer retirement while preserving routing and surviving lists. The actual receive-worker iteration discharges condResched. `original_session_routing_frames`, `original_handshake_receive_routing_frames`, `original_handshake_routing_completion`. |

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
[AGENT 2026-10-14] Compose the public command as a literal observer, retaining
CompletionAcquired across a named acquisition suffix rather than changing its
result representation. Propagate actual parser output through separate checked
list/array and suffix contracts; an rfl source equation preserves all parser
branches while avoiding repeated continuation expansion.


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

The complete public peer-command contract now derives residency through actual
lookup/create outcomes, retaining ordinary errors and earlier completed effects
on later Stop. Successful public parseTrace proves all configured peers' address
shape, preserving malformed alternatives and device-selector updates.

The complete device observer now covers lookup/flag/permission guards, fwmark/port
updates, replacement of all peers, private-key changes and the saved peer-attribute
loop. A clear completion occurs immediately after actual WG.free, before capture
of the remove-all list and both original loops. Normal remove-all leaves folded
flat tables empty; a later stale-entry or flush Stop retains the earlier clear.
Private-key replacement keeps lookup→peerPut→peerRemove order, dropping acquired
residency before the put. Saved staged sends use deletion-permitting routing frames.
Ordinary negative results retain preceding completed changes and actual cleanup.
[AGENT 2026-10-14] Extend the existing primitive completion sum with clear at its
actual WG.free boundary; compose original DeviceSource continuations with concrete
silent frames, retaining an empty-fold postcondition for later lifecycle use.

Optional routing now preserves the existing present-device contracts while adding
absence with empty folded tables. Guarded original creation either retains routing
or installs an empty device from absence. Original down permits peer deletion;
destruction observes the real clear/remove-all before lifting its unchanged queue,
sleep and ratelimiter suffix to the final device drop. No synthetic reset is added.
Whole absent peer/device commands preserve exactly their entry journals, even if
an arbitrary fixture row makes interface lookup succeed. Direct invalid setAllowedip
can still complete while absent; it is not covered by that whole-command fact.
All typed initial fixture modes and successful seccomp prefill establish optional
routing. These are source-derived local contracts, not enclosing Runner execution.
[AGENT 2026-10-14] Keep present completion validity unchanged and add an optional
routing state; use the actual clear's derived empty fold before final device drop,
and the guarded creation endpoint for fresh empty routing.

**Silent traffic frames.** Original lookup borrowing preserves the routing view;
TX completion/worker, wgXmit, concrete Stack delivery, RX completion/poll and decrypt
iteration retain the table/frontiers and each surviving resident list. Original
peerPut may delete residents. Cached setters use actual getter-produced list facts;
no ownership, affiliation, credit, address-bound, packet-validity or drain premise
is added. Arbitrary checksum, GRO, IRQ, softirq and rescheduling callbacks require
routing frames; actual checksum and Stack callbacks are discharged. Whole-call
lifts leave the completion journal unchanged on all outcomes and derive normal
optional-state preservation; a Stop supplies no failed World or packet authorization.
[AGENT 2026-10-14] Reuse exact traffic source cuts and prove deletion-permitting
routing frames for whole-call lifting. Preserve cached-list facts only across
concrete equality frames, and share the existing endpoint matcher environment
to avoid duplicate generated declarations under Lean 4.35.

**Concrete admission and maintenance.** Actual consumeData/wgReceive includes
index-reference acquisition, EPIPE publication and ENOSPC release without assuming
key/peer affiliation. Both NAPI poll callers and IRQ-exit placement now instantiate
the actual Stack callback; encrypt/decrypt/tx iterations use the actual checksum,
softirq, IRQ and condResched calls. All five timer callbacks and device open/up/
namespace exit retain routing, including ordinary errors and possible peer deletion.
Every later cached setter uses its actual getter; no saved-list validity is assumed.
[AGENT 2026-10-15] Close the concrete callback callers with the existing routing
relation and exact source helpers, keeping receive admission separate from
handshake processing and the enclosing scheduler. Whole-call lifts require no new
completion event because these operations preserve the routing configuration.

**Handshake routing boundary.** Keypair creation/replacement, key derivation,
index replacement, beginSession, response creation and sending retain routing
and every peer allowed-IP list on normal return. Incoming initiation/response,
cookie consumption and handshake receive use the weaker deletion-permitting
relation because original cleanup may retire a peer. Every later setter takes
its witness from an actual getter. The actual receive-worker iteration uses the
original condResched; no resident, affiliation, credit, valid-message or drain
premise is introduced. Silent lifts erase exactly and preserve optional routing
on normal return, retaining unchanged prior safe history on Stop without a failed World.
[AGENT 2026-10-15] Reuse the checked Cookies.receive_factor/loadPhase boundary and
split only its MAC/switch continuation locally. This keeps source reductions
bounded without changing operations or proof limits; cookie projections and
fresh getter facts establish routing preservation independently of ring frames.

**Remaining obligations.** Compose the actual syscalls and Runner with the optional
state and lifecycle observations. Complete activation/scheduler, timer dispatch,
enclosing environment and syscall routing frames remain required;
concrete NAPI/admission/timer-callback/device-control frames are supplied above.
A failing clear has no returned World or successful completion marker; earlier
partial mutations are outside a completed-call history. Literal contiguous
histories cannot span unobserved guards/helper effects. The earlier tagged
preparation equation was removed after elaboration failures; the current literal
observer closes that public-command boundary without an output-invariant or
target-residency premise. Connect packet paths to authenticated allocation identity;
raw peer labels and longest-prefix lookup alone establish no ownership.
Independent path inspection identifies the remaining public-key-table binding
(resident entries agree with peer.remoteStatic), index/key-slot/packet affiliation,
and TX packet shape derived from the actual constructors. Allocation safety alone
does not supply these facts. RX authorization is at consumeDataDone; TX handoff
is the actual staged append, before later failure or deferred transmission.

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
| Acquired-peer removal/update completion | 30 calls: 29 builds (8 PASS / 21 ordinary elaboration/normalization FAIL) plus one passing scope/census check; final scoped/full targets 278/397 | 30m40s from grant 15:30:16 through final full-result collection clock 16:00:56. Four exports, 90 R3 /400 source declarations. No cap/interruption; all exits collected. The complete acquired stage and concrete flush/acquisition foundations compile; repeated preflight continuation-normalization failures left whole setPeerCmd composition open at that checkpoint (closed by the later literal observer). No runtime change/replay. Independent frozen review and coordinated gate/fresh replay/default/unit validation pass. Token returned at 16:02:40 (32m24s ownership). |
| Public peer command and parsed address shape | 33 capped calls: 32 builds (7 PASS / 25 ordinary FAIL) plus a passing exact scope/compatibility check; scoped/full 286/425 | 45m06s from measured grant 20:18:48 through full-result measurement 21:03:54 UTC. Three exports; 93 R3 / 423 source declarations. Failures were elaboration/normalization and deterministic tactic limits, including the public-command mutable join and parser continuation expansion; literal acquisition and parser suffix cuts close both without changing source or premises. All exits collected, no cap/interruption, recovery admission diagnostic or runtime replay. The exact check preserves all 420 prior declaration statements/proof bodies and confirms five-file scope, census, whitespace and mirror equality. Literal source cuts retain all original errors and Stops; no added target-residency, parser-fidelity, credit or progress premise. Independent frozen review is clear, with no finding. Token returned at 21:08:52 (50m04s ownership). Sequential coordinated proof gate, fresh stock kernel replay, default build and 124 unit tests pass; the capped exact scope/hash/census/compatibility/whitespace/mirror check also passes. |
| Complete device routing completion | 12 capped calls: 10 builds (4 PASS / 6 ordinary FAIL) plus two passing exact checks; scoped/full 289/433 | 9m00s from measured grant 22:07:48 through full-result measurement 22:16:48 UTC. Three exports; 96 R3 / 432 source declarations. Failures were local projection/bind normalization, one namespace qualification, list-proof subgoal ordering and an empty-fold rewrite. The first failed build also rejected a declaration containing metavariables; no source admission or recovery `declaration uses sorry` diagnostic occurred. No cap/interruption or runtime change/replay; all exits collected. The exact check preserves all 429 prior declaration statements/proof bodies and confirms scope, census, whitespace and mirror equality. Independent source/export review found no defect; its low stale-scope finding in two map passages and one old terminal comment is corrected, preserving every declaration statement/proof body. The coordinator gate rebuilt the final comment-only edit. Final independent documentation reconciliation is clear. Sequential coordinated gate (433 jobs, 432 permitted-axiom declarations), fresh stock kernel replay, default build (60 jobs), unit tests (124, 22.031 seconds, one skip) and capped exact scope/hash/census/compatibility/whitespace/mirror checks all pass. Token handback clock 22:21:52 UTC (14m04s ownership); all 12 named logs removed and no active jobs. |
| Optional routing and device lifecycle | 14 capped calls: 11 builds (3 PASS / 8 ordinary FAIL), three exact checks (FAIL / PASS / PASS); scoped/full 293/439 | 9m31s from measured grant 22:41:55 through full-result measurement 22:51:26 UTC. Three exports; 99 R3 / 440 source declarations. Failures concerned cached-peer-list/let normalization, namespace and private-predicate inference, history equality direction, an extra scope terminator and a getK leaf. Calls 5 and 8 explicitly reported kernel-rejected metavariable placeholders; no source admission or recovery `declaration uses sorry` diagnostic was introduced. No cap/interruption or runtime change/replay; all build exits collected. Check 12 failed because its temporary token scan included comments and matched an existing English verb; check 13 reuses the actual gate's comment-aware token/import routines and passes. Check 14 confirms the final review metadata and frozen hashes. All 437 prior terminal statements/proof bodies are unchanged; exact six-file scope, census, whitespace, empty index and mirror equality pass. Independent frozen source/export/documentation review is clear. Sequential coordinated proof gate, fresh stock kernel replay, default build, 124 unit tests and exact scope/hash/compatibility checks pass. Token returned 22:56:55 UTC (15m00s ownership); all 14 worker logs are removed. The coordinator staged-whitespace check then rejected a trailing blank line in the new lifecycle file; removing it changes no compiled code. The corrected staged check passes. The coordinator also corrected the stale pending-validation register cell before commit. |
| Silent TX/Stack/RX routing frames | 11 capped calls: 9 builds (5 PASS / 4 ordinary FAIL), two exact checks (FAIL / PASS); final scoped/full 313/444 | 8m05s from measured acceptance 23:22:31 through full-result collection 23:30:36 UTC (root grant 23:22:00). Three exports; 102 R3 / 446 source declarations. Failures concerned explicit frame arguments, projection/exception normalization, private-function inference and retaining a cached peer-list fact. The first full build failed on a duplicate generated matcher auxiliary shared with TxDispositionEndpoints; importing its existing environment closes the collision without changing a source operation or theorem premise. No heartbeat/recursion/cap/interruption, admission/recovery-placeholder diagnostic or runtime change/replay. All exits collected. Check 10 failed because the temporary mirror comparison omitted the existing proof root Leanux/Proofs.lean from its exclusions; check 11 corrects that scope and passes. Exact five-file scope, all 443 prior terminal statements/proof bodies, census, whitespace/EOF, empty index, comment-aware tokens/imports and mirror equality pass. Independent frozen source/export/documentation review is clear. Sequential coordinated gate (444 jobs, 446 permitted-axiom declarations), fresh stock kernel replay, default build (60 jobs), units (124, 23.041 seconds, one skip) and exact frozen checks pass. Token returned 23:34:59 UTC (12m28s from acceptance; 12m59s from grant); all 11 worker logs and the temporary check script are removed. |
| Receive admission, concrete NAPI and maintenance routing | Nine capped calls: seven builds (4 PASS / 3 ordinary FAIL), two passing exact checks; scoped/full 318/450 | 5m30s from measured acceptance 2026-10-14 23:56:13 through full-result collection 2026-10-15 00:01:43 UTC (grant 23:55:50). Three exports; 105 R3 / 453 source declarations. Failures were ambiguous helper qualification, a multiline structure-update layout, and the inline-poll loop invariant; the latter printed tactic-recovery placeholders in rejected goals, with no source admission or declaration-uses-sorry diagnostic. No cap/interruption, heartbeat/recursion failure or runtime change/replay. All build exits collected. Command-scoped LEAN_NUM_THREADS=32 retains the default cap; no global setting changed. Exact six-file scope, all 450 prior terminal statements/proof bodies, census, whitespace/EOF including untracked files, empty index, comment-aware gate tokens/imports and mirror equality pass. Independent frozen review is clear. Its map wording finding is fixed: optional state is preserved on normal return; Stop retains only prior safe history, without a returned World. Root's stale R4 enclosing-worker scope phrase is corrected to enclosing run coverage. Coordinated gate (450 jobs, 453 permitted-axiom declarations), fresh stock kernel replay, default build (60 jobs), units (124, 22.983 seconds, one skip) and exact frozen checks pass. Token returned 2026-10-15 00:06:17 UTC (10m04s after acceptance; 10m27s after grant). All nine call exits are collected. |
| Session and handshake receive routing | Twelve capped calls: ten builds (5 PASS / 5 ordinary FAIL), two passing exact checks; scoped/full 321/455 | 9m11s from measured acceptance 2026-10-15 00:25:48 through full-result collection 00:34:59 UTC (grant 00:25:06). Three exports; 108 R3 / 460 source declarations. Failures concerned projection/zeta normalization, a missing explicit import, cookie factoring, ambiguous WG.andM/orM and the workerIter namespace. Call 3 hit the default recursion limit during branch-World expansion; canonical branch frames avoid it. Call 5 hit the existing 1,000,000-heartbeat limit and its dependent theorem reported a kernel unknown constant; the checked source cut closes the proof without raising limits. Call 6's ambiguous terms caused rejected recovery placeholders and a declaration-uses-sorry diagnostic; no source admission was introduced, and the corrected scoped/full builds pass. No cap/interruption or runtime change/replay. All exits collected; command-scoped 32-thread Lake parallelism retains the default cap and per-Lean -j1. Exact six-file scope, all 457 prior terminal statements/proof bodies, census, whitespace/EOF including untracked files, empty index, comment-aware gate tokens/imports and mirror equality pass. Independent frozen review is clear; its retained report-row wording finding is fixed to distinguish normal-return state from all-outcome journal/Stop history. An initial prose-edit assertion failed before write and was corrected against the actual sentence. Coordinated gate (455 jobs, 460 permitted-axiom declarations), fresh stock kernel replay, default build (60 jobs), units (124, 24.034 seconds, one skip) and exact frozen checks pass. Token returned 00:37:40 UTC (11m52s after acceptance; 12m34s after grant); all twelve call exits are collected. |

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
| `Logged/ProjectsUnderTo`, `StampedGro`, `RxPollJoint*`, `RxPollStampSafety`, `RxPollStampPhase` | One stamped execution has exact original/GRO erasure and direct allocation-conditional lifetime projection. Fresh local metadata retains arbitrary valid prior lifetime history; capture/removal/release phases and full GRO payload provenance prove per-poll removal/callback stamp uniqueness on failed prefixes and actual releases on normal completion. |
| `RxWorkerCuts`, `RxWorkerHistory`, `RxActivationHistory` | Concrete encryption/decryption callbacks, transmit pre-encryption and one activation iteration use the persistent stamped observers. Exact original erasure, direct focused-R2 projection at the same incoming history, normal boundaries and failed-prefix entry uniqueness. |
| `RxActivationRunHistory`, `RxScheduleHistory` | Actual activation runs, dispatch, scheduling and nested rescheduling carry stamped committed polls, direct full R2 audit correspondence and exact reached-filter probes; candidate trial histories stay isolated. |
| `RxEnvWorkersHistory`, `RxEnvTrafficHistory`, `RxEnvBatchHistory` | Actual deferred workers, ingress, both flood modes and batch processing retain all reached stamped scheduler/poll calls and directly project to the same incoming full R2 audit. |
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

[AGENT 2026-10-14] Prove per-poll duplicate freedom before enclosing conservation.
Capture allocation identity from the same original second packet getter, focus the
existing lifetime observers, and carry the stamp with exact GRO bytes. Use direct
mapped-result projections, a fresh local GRO journal and prior valid lifetime
history; independent source erasures do not establish journal agreement. Separate
capture/removal/release phases from payload provenance, permitting a pending stamp
on Stop and held callbacks after earlier packet release.

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

**Joint stamped poll.** The observer wraps the original second successful
`getRxSkb` immediately before queue removal and captures `(ifindex, skb + 1)`;
it adds no getter. Every original getter, put, free, decision, callback and Stop
is retained. One execution projects unconditionally to `WG.rxPoll` and to
`RxPollGro`, and directly to `rxPollStackPrefix` under the existing `AllocationInv`.
The latter projection transports that invariant through concrete intermediate
contracts and maps the GRO accumulator result explicitly.

A poll starts with no local occurrence events and any valid prior lifetime history.
The capture/removal/release phase proof derives freshness from the actual getter,
keeps the captured device ifindex through the existing full ring-cell frames, and uses the
actual free's read/release observations before another iteration returns to Ready.
Every reached removal stamp is distinct, including on Stop. Normal poll return
has an observed release for every removed stamp. This does not assume distinct
queue IDs, per-iteration freshness or release; malformed aliases may instead Stop.

A separate journal invariant of this same observer retains the complete
occurrence/slot/stamp key through both GRO lists and every callback entry. Every
entered key belongs to an actual removal. Removal-stamp uniqueness and the existing
exactly projected callback-ordinal uniqueness give callback-stamp uniqueness within
one poll. Normal completion has released every entered stamp. Buffered GRO bytes
may be handed off after their packet storage was released. The entry event occurs
before the focused original stack callback and remains visible if that callback
Stops; it is not a successful-delivery marker. `rxPollFree = false` also includes
`consumeDataDone = none`, and the final packet free runs for drops and GRO handoffs.
These control distinctions are retained, without treating the flag or free as a
semantic drop disposition.

**Capture suffix and finite composition.** A separate pure journal invariant
now connects each removal key to the matching original capture read before that
removal, inside the new suffix. Full stamped callback provenance carries this
support to entered payloads. This source-support statement is unconditional;
AllocationInv and the directly projected safe lifetime history then exclude any
release of that stamp in the incoming history. On normal return, every removal
and entry has an actual release in this suffix, including explicit drops which
produce no GRO entry. No freshness or release behavior premise was added.

The persistent observer retains all earlier audit/probe and poll events. It runs
each poll with fresh local metadata seeded by exactly the current projected
lifetime history, and appends only its new suffix. A direct projection proves
agreement with auditFocus(rxPollStackPrefix) at that same history, including
Stops and interleaved saved probes. Erasure and Appends are not used to assume
history neutrality. The normal-boundary invariant combines audit validity,
entry-stamp distinctness and releases of all completed entries. The failed-prefix
condition retains audit safety and distinctness, without a release obligation
for a callback which stopped. Buffered bytes may still be entered after their
packet allocation's earlier release. Local ordinals restart at zero and are
never treated as global occurrence identifiers.

The boundary contracts compose finite sequences of the original polls and
preserve already recorded entries through a focused audit observer. The latter
frame does not certify callback coverage: an audit callee can contain real polls
whose entries that wrapper does not record. Copied consistency trials remain
separate from committed entries. Callback entry still does not mean completed
stack delivery. [AGENT 2026-10-14] Prove the missing read-support bridge as a pure
journal invariant and append fresh local poll suffixes at identical lifetime
histories; this reuses the existing allocation/cell phase and avoids a stronger
history-independence assumption.

**Direct NAPI callers.** `RxNapiHistory` now invokes the stamped poll at both
actual direct sites: `Env.napiSoftirq` and `Env.pollScheduledInline`. The IRQ-exit
wrapper observes its actual true-arm softirq rescan. The complete captured-map
filter scan remains before the empty/hidden/multi-peer guards; IRQ's `any` scan
short-circuits, and placement is consumed only after its three guards. Inline
polling adds no section wrapper. NET_RX start, ordinal installation, normal
section reset and stop remain in their original order; a body Stop retains its
prefix without executing the closing operations.

Three grouped terminal contracts give unconditional source erasure, direct
projection to the existing focused R2 caller at the identical incoming lifetime
history, and normal-boundary/failed-prefix preservation. Interleaved saved probes
are preserved. Empty-history safety needs only local AllocationInv, not an
assumed callback, freshness or successful return. Focus composition uses actual
lower append contracts and transports the allocation invariant through continuations;
independent erasures and history neutrality are not used. No additional getter,
source action or speculative delivery event is inserted. Callback entry remains
attempted handoff, including an entry followed by callback Stop.

[AGENT 2026-10-14] Factor the scan and section wrappers in the proof tree and
reuse existing lower preservation for conditional focus composition, avoiding a
second lifetime observer or a stronger unconditional-append assumption.

**Concrete crypt workers and activation.** `RxWorkerCuts` factors encryption's
initial softirq from its nonpolling checksum/encryption/reschedule tail. The
softirq remains before the empty-queue test. Its RX publication cut retains the
original packet/keypair getters, peer reference acquisition, cached peer read,
queue-membership guard, packet write and cached NAPI setter. The actual getter
supplies the setter's identity condition. The IRQ observer then runs before the
original peerPut; that callback may already remove/free the published packet.
There is no new residency or raw-reference affiliation premise.

`RxWorkerHistory` observes decrypt's initial softirq, publication IRQ placement
and trailing softirq. Original consumed/decrypted decisions, successful packet
replacement, DEAD publication, reschedule and failure propagation remain exact.
A callback Stop retains its actual prefix and skips later puts or releases.
`RxActivationHistory` covers cryptAhead's hidden-record and TX-head guards, real
peer/TX getters, suspended-encrypt lookup, temporary TX-work-queue append/erase,
observed encrypt iteration and suspended iteration update. Its empty/yielded
late Stops remain after their original source actions. One Activation.iter then
composes encrypt/decrypt, cryptAhead before TX, the poll-free TX/receive observers
and all unsupported-worker or missing-peer failures.

The four grouped exports give unconditional original erasure, direct projection
to the existing focused R2 observer at exactly the incoming audit history, and
persistent BoundaryInv/failed BoundarySafe preservation. The direct bind rule
uses actual lower allocation/append contracts through each continuation; it does
not infer history neutrality from source erasure. Prior probe markers remain
interleaved. Only the empty-history corollary requires local AllocationInv.
Normal return restores the entered-stamp release boundary; failed prefixes retain
entry uniqueness without a release endpoint or failed World. Entry still means
attempted callback handoff, not successful delivery. The enclosing activation
run/dispatch/scheduler and saved consistency-filter probes are covered separately
below; trial callback entries remain isolated.

[AGENT 2026-10-14] Reuse existing poll-free lifetime observers and factor exact
publication/callback boundaries, keeping observed NAPI calls explicit. This avoids
copying lower packet operations or silently hiding a poll in a focused whole call.

**Complete local scheduling.** `RxActivationRunHistory` retains the actual
observed occupancy read, occupancy-plus-one bound, mutable activation iterations,
section-stop consumption, suspended append on yield and exhaustion Stop. Dispatch
keeps each empty/default refusal, TX unit resolution and queue erase before its
section start and observed activation run. The finite-loop projection transports
the actual continuation history through the existing allocation/append contracts;
source erasure is unconditional.

`RxScheduleHistory` follows the existing R2 audit scheduler's control literally.
It retains the no-record worker order, record-driven bound, dispatch guards,
NET_RX test, post-poll record check, exact single-candidate resumption, optional
stack-worker ambiguity check and all Stops. Pending-NAPI and has-work controls use
the actual lower read observers, preserving the original eager device read and
short-circuit saved-peer scan. Nested rescheduling consumes the original worker
choice and invokes the observed scheduler only on its true arm.

Each actual consistency-filter entry uses the existing focused filter audit,
which captures its current World and lifetime history before the original copied
trials. The marker survives an empty filter or a later Stop. Direct projection
is to `scheduleAudit`, retaining complete probe payloads and interleaving, not
merely its lifetime-only projection. Existing saved-probe contracts give each
reached entry's allocation invariant, exact ordered filter decisions and safe
isolated candidate histories. Candidate callback entries are never appended to
the committed stamped journal. A failed committed callback retains its entry and
prefix; only normal return restores the released-entry boundary.

The four grouped exports provide exact original erasure, direct audit projection
and concrete BoundaryInv/failed BoundarySafe preservation. Only their separate
empty-history corollaries require local AllocationInv. These remain local caller
contracts, not initialized Env/Runner coverage, successful stack delivery or
receive-pipeline conservation. [AGENT 2026-10-15] Keep a literal audit-aware
scheduler in the proof tree: the older ring-oriented SourceScheduler raw lifts
control reads and omits actual probe markers, so its independent erasure cannot
supply this direct audit correspondence.

**Concrete environment traffic callers.** The new observers cover runCryptWorkers,
runSendWorkers, afterXmit, inject, flood, afterBatch, batchItem and batch. They
invoke the concrete stamped scheduler at every actual deferred scheduling call.
Both recorded flood branches use the original bounded receive-worker loop with
its real nested-reschedule callback, reached only after a handled item. The
hidden-none shortcut, queue replacement, counter arithmetic, record cuts, section
stops and late threshold refusal are retained. Queue replacement/reset use their
existing allocation-safe audit contracts; they are not assumed unchanged Kernel.

Batch ingress retains wgReceive followed by the stamped inline poll inside one
NET_RX section. The actual section-start ordinal, active-section installation,
normal clear and section-stop order remain unchanged. A callback Stop retains
its journal prefix without executing the later clear/stop or CQE update. Batch
route-error CQEs, captured device scalars, multicast handling and deferred-send
order are preserved. Focused leaves cover inspected poll-free source paths;
loopback refuses pending NAPI rather than running a hidden poll.

Four grouped exports give unconditional original erasure, direct projection to
the corresponding existing full R2 audit at the exact filtered incoming journal,
and concrete BoundaryInv/failed BoundarySafe preservation. Existing probe markers
and their payloads survive; copied trial entries stay isolated. Only separate
empty-history corollaries require local AllocationInv. No successful drain,
residency, credit, progress or history-neutrality premise is added. Callback entry
remains distinct from successful stack delivery. [AGENT 2026-10-15] Reuse exact
poll-free R2 leaves and the existing worker/NET_RX loop wrappers; expand each
poll-bearing environment caller so the new journal observes its actual callbacks.

**Remaining obligations.** Initialized whole-schedule duplicate freedom needs
the enclosing concrete caller spine to connect the persistent stamped journal to
R2's initialized Runner audit. Whole-call access frames alone do not observe
nested callbacks. RX carrier preservation through relevant transmit
callbacks, enclosing timers/observation/runner/lifecycle, worker-local ownership and joint
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
local poll ordinals alone do not establish cross-poll uniqueness; finite composition
uses capture-read freshness and prior release observations instead. Universal outgoing
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
| Joint stamped rxPoll | 32 capped calls: 30 builds (13 PASS / 17 FAIL) and two passing exact checks. Failures included simplifier recursion depth at call 10 and the existing 2,000,000-heartbeat limit at call 20; narrower composition and explicit bind adapters closed them without raising limits. Every exit is collected; no memory-cap failure. | Grant 21:15:22 UTC; full-target collection 21:50:33 (35m11s), token return 21:59:01 (43m39s ownership). Scoped/full 257/431; frozen review and final documentation reconciliation are clear after the reporting amendment. Sequential coordinated proof gate, fresh kernel replay, default build, 124 unit tests and exact scope/hash/compatibility checks pass. All seven frozen Lean hashes are unchanged. |
| Capture suffix and finite poll composition | 13 capped calls, 11 builds (6 PASS / 5 ordinary FAIL) and two passing exact checks; scoped/full 261/436 | Grant 22:27:43 UTC; full-result collection 22:34:04 (6m21s); token returned 22:37:34 (9m51s ownership). Five exports, 90 R4 / 437 source declarations. Failures were local reserved-field/identifier syntax, list/filter normalization, dependent bind/loop inference and a let-unfold repair. No cap/limit failure, interruption, source admission or runtime change/replay; all exits collected. The exact check preserves all 432 prior declarations and confirms scope, census, whitespace, source tokens/imports and mirror equality. Independent frozen review is clear at 22:36:44 UTC with no finding. Sequential coordinated proof gate, fresh kernel replay, default build, 124 unit tests and exact scope/hash/compatibility checks pass. All four frozen Lean hashes are unchanged; all 13 worker logs are removed. |
| Direct NAPI callers | 17 capped calls: 13 builds (8 PASS / 5 FAIL), four exact checks (FAIL / PASS / PASS / PASS); scoped/full 283/442 | Acceptance 23:05:30 UTC; final full-result collection 23:14:55 (9m25s). Three exports, 93 R4 / 443 source declarations. Call 1 failed at the existing simplifier recursion limit after a self-rewriting equation; directed rewrites close it. Call 6 failed at the existing 200,000-heartbeat limit in expanded softirq focus; factoring the exact section wrapper closes it without raising limits. Other failures were dotted-constructor inference, tactic-macro hygiene/parser and explicit history-parameter inference. No source admission, recovery placeholder diagnostic, cap/interruption or runtime change/replay. Every exit is collected. Check 12 failed because its temporary script required zero from a clean new-file `git diff --no-index --check`, whose difference exit is one; checks 13/16 accept the normal difference status only with empty diagnostics and independently inspect every line and EOF. The exact six-file check preserves all 440 old terminal bodies and confirms census, empty index, whitespace, source tokens/imports and mirror equality. The exports keep the allocation premise inside only the local empty-history corollary; erasure, direct conditional projection and invariant preservation remain unconditional contracts. Independent frozen review is clear with no finding (final pass 23:16:15–23:16:32). Final metadata/hash check 17 passes. Token returned 23:17:24 UTC (11m54s from acceptance; 12m19s from root grant at 23:05:05); all 17 worker logs are removed. Sequential coordinated proof gate (442 jobs, 443 permitted-axiom declarations), fresh stock kernel replay, default build (60 jobs), unit suite (124, 22.155 seconds, one skip), and exact frozen-hash/scope/compatibility/census/whitespace/mirror checks pass. All four frozen Lean hashes remain unchanged. |
| Concrete crypt workers and activation iteration | Eight capped calls: seven builds (4 PASS / 3 FAIL), one passing exact check; scoped/full 286/447 | Root grant 23:39:17 UTC, measured acceptance 23:39:31; full-result collection 23:48:38 (9m07s after acceptance). Four exports; 97 R4 / 450 source declarations. Calls 1 and 2 failed at the existing 200,000-heartbeat limit in broad factorization scripts and also reported branch-normalization, an unavailable tactic and unreachable-Stop frame goals; directed bind/case proofs close them without raising limits. Call 5 failed on get/suspended-bookkeeping allocation frames because restricted transparency prevented their reduction; the existing concrete unchanged-Kernel proof closes them. No cap/interruption, source admission, recovery-placeholder diagnostic or runtime change/replay. All exits collected. Call 8 checks exact six-file scope, all 446 prior terminal statements/proof bodies, census, whitespace/EOF including untracked files, empty index, actual comment-aware gate tokens/imports and mirror equality. Independent review found two stale current census rows in the proof register; both are corrected to 97 R4 and 450 total declarations. Revised independent review is clear at 23:50:40 UTC. Coordinated gate (447 jobs, 450 permitted-axiom declarations), fresh stock replay, default build (60 jobs), units (124, 23.045 seconds, one skip) and exact frozen checks pass. Token returned 23:50:54 UTC (11m23s after acceptance; 11m37s after grant); all eight worker logs are removed. |
| Complete local scheduling | Six capped calls: four builds (2 PASS / 2 FAIL), two passing exact checks; scoped/full 288/452 | Root grant 2026-10-15 00:10:46 UTC, acceptance 00:11:04; full-result collection 00:16:14 (5m10s after acceptance). Four exports; 101 R4 / 457 declarations. Call 1 failed on focused-loop type alignment and contradictory duplicated dispatch matches; direct list induction and contradiction normalization close these. Call 2 compiled run/dispatch but failed at the existing 200,000-heartbeat limit in the scheduler projection's final broad congruence search; normalizing the fixed worker selection before directed projection closes it without raising limits. No cap/interruption, source admission, recovery-placeholder diagnostic or runtime change/replay. All exits collected. Call 5 checks exact scope, all 453 prior terminal statements/proof bodies, source/register counts, whitespace/EOF including untracked files, empty index, actual gate tokens/imports and mirror equality. Preliminary review identified the old activation-iteration scope comment as stale; its comment-only correction points to scheduler composition while keeping initialized Env/Runner and delivery open. Independent frozen source/export/documentation review is clear (00:17:45–00:19:19), with no unresolved finding. Final metadata/hash check 6 passes; coordinated gate (452 jobs, 457 permitted-axiom declarations), fresh stock kernel replay, default build (60 jobs), units (124, 23.011 seconds, one skip) and exact frozen checks pass. Token returned 00:19:58 UTC (8m54s after acceptance; 9m12s after grant); all six call exits are collected. Builds use command-scoped LEAN_NUM_THREADS=32 for Lake scheduling; the unchanged project -j1 still applies to individual Lean processes. |
| Concrete environment traffic callers | Nine capped calls: six builds (3 PASS / 3 FAIL), three passing exact checks; scoped/full 293/458 | Root grant 2026-10-15 00:41:54 UTC; acceptance 00:42:19; full-result collection 00:52:18 (9m59s after acceptance). Four grouped exports; 105 R4 / 464 declarations. Call 2 failed on receive-step projection specialization and reflexive Kernel goals; explicit typed lower contracts and reflexivity close them. Call 3 compiled traffic but three batch projections failed at the existing 200,000-heartbeat limit in broad nested preservation search; flat concrete leaf contracts and directed bind/loop projection close them without raising limits. Call 4 compiled the batch module but failed on an unqualified BatchItem export binder; explicit Leanux.Env qualification closes it. No source admission, recovery-placeholder diagnostic, cap/interruption or runtime change/replay. All build exits collected. Exact checks preserve all 460 prior terminal statements/proof bodies, six-file scope, empty index, actual census, comment-aware gate tokens/imports, whitespace/EOF including new files and mirror equality. Independent review found a stale secondary R4 claim-boundary row omitting the four Env exports and still listing enclosing ingress as open; the row now lists all four exports and the precise remaining timers/observation/lifecycle/initialized Runner scope. The correction is independently verified; frozen review is clear with no unresolved finding (00:53:48–00:54:32 UTC). Coordinated gate (458 jobs, 464 permitted-axiom declarations), fresh stock kernel replay, default build (60 jobs), units (124, 23.730 seconds, one skip) and exact frozen checks pass. Token returned 00:55:23 UTC (13m04s after acceptance; 13m29s after grant); all nine call exits are collected. Builds use command-scoped LEAN_NUM_THREADS=32 for Lake scheduling, retaining the unchanged default cap and individual Lean -j1. |

Failed joint-poll calls 16 and 23 also printed Lean elaborator-recovery
`sorry ()` / `[sorry]` goal terms after ambiguous constructor/type errors and an
unknown substituted identifier. These were failed-elaboration placeholders in
error diagnostics, not source proof admissions; both calls failed. The corrected
257-job scoped and 431-job full builds pass, and the exact source token check
passes. Coordinated axiom checking on all 429 declarations and fresh stock kernel
replay also pass. The worker removed its 30 exact log files; calls 01 and 32
returned directly without separate files.

Failures were elaboration/replay assertions, plus the noted phase heartbeat
timeout; the RX scoped check rejected the
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
