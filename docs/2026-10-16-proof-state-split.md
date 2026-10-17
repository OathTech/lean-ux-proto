# Proof campaign: state-split retrofit

The campaign branch contains main `b700659`, including the split at `6089dc4`.
The executable mirror remains byte-identical to that landing. This branch keeps
the nondefault `LeanuxProofs` target and `scripts/proof-gate`, which return with
the proof tree. The [split design](2026-10-15-design-state-split.md) governs the
new worlds; new R3/R4 results follow the retrofit.

## Counts and status

| Census | Lean files | Named theorems |
| --- | ---: | ---: |
| Validated baseline `00641c6` | 471 | 7,715 |
| Completed retrofit checkpoints | 452 | 6,544 |

Completed changes comprise **2,890 retyped/generalized, 1,704 deleted,
1,913 retained contract shapes and 533 added theorems**. Retyping changes the
actual carrier or observation, including shorthand contracts whose functions
move to a native monad. Namespace-only product qualification and equivalent
projection relocation count as retained. The census includes private and
attributed declarations and excludes nested comments, strings and tactic-local
variables. Uncommitted work is outside these totals.

The terminal surface has 515 declarations: 513 theorems and two definitions.
**All seven register rows remain lagging**, last fully validated over `cb2348e`.
The complete proof gate and terminal kernel replay have not passed over the
split. R1/R2/R5/R6 retain their earlier charter dispositions subject to the carry;
initialized R3 packet authorization and R4 receive-pipeline conservation remain
open. The [register](proofs.md#results) is authoritative for result scope.

## Contract preservation

Concrete leaves use their actual WG, FS, Seccomp, Task and Ambient stacks;
the runner retains the product World. Native observations expose both WG and
Ambient endpoints. Stops retain the reached history without inventing a
returned state. Arbitrary callbacks and action modifiers retain product scope
or a generalized actual-state contract.

The baseline store mask contains 43 fields, including seven WG fields. It is
distinct from the incoming 47-field observation that adds routing and timer
state. Earlier narrowed generic helper domains and stronger modifier premises
were rejected and repaired: all 26 identified generic helpers plus
snapshot_modify retain their original arbitrary-action scope. Native
counterparts supplement them. The WG initialization premise observes the
original store view, not equality of unrelated routing/timer fields.

Deleted frames follow actual write boundaries: foreign-subsystem facts,
component-only Skb/Index/Ambient updates, redundant adapters and support used
only by deleted layers. Native own-store lookup, mutation and lifetime facts
remain substantive proofs. Removed seccomp-prefill WG facts are justified
because the function receives only SeccompWorld and TaskWorld. A failed
compilation is never the deletion argument.

Proof-side source copies had drifted before the split. Their repairs retain
actual getter/decision order, timer wheel selection, callbacks, routing checks,
batch completion, full copied-world trials and exact JSON/indexed Stops.
The [findings and reproduction commands](2026-10-16-proof-state-split-findings.md)
preserve the checked counterexamples and distinguish them from Linux claims.
No mirror change was made to close a proof.

## Validation and remaining work

Completed checkpoints have scoped builds, explicitly enumerated axiom checks,
fresh module replay and independent complete source reviews. The latest runner
checkpoint carries 13→19 theorems: twelve original product contracts retained,
one type-derived seccomp-prefill frame deleted and seven private composition
helpers added. Both original trace/placeholder domains remain, including Stops,
full failure journals, saved trials and actual returned World projections.
The eight original routing contracts retain their parser-shape premise.
Four existing timer-dispatch declarations become public without type/body
changes so the stamped timer observer can reuse them.

The runner modules build in 2.3 and 2.5 seconds, with zero own warnings.
All 23 named runner declarations and the four newly public timer declarations
have standard axioms only; fresh closure replay and independent complete source
review pass. The preceding material/scheduler/worker checkpoint passes its
355-job graph and all eighty named declaration checks and fresh replays.

The unchanged executable closure previously passed the model build (66 jobs),
executable build (130 jobs) and unit suite (131 tests, one skip). These passes
do not validate the unfinished proof tree. Older proof modules still contain
deprecated tactics and unused-simp warnings; those remain migration work.
Lean 4.35's vcgen is a different implementation from mvcgen, so a blind rename
does not preserve the existing proof scripts.

CounterWindow/Refinement's warning cleanup preserves all statements and
premises. Its 31-job scoped build, all 24 named declaration axiom checks,
fresh kernel replay and independent source review pass, with zero own warnings.
One changed-source development check failed before the final cleanup passed.
This proof-body maintenance does not change the retrofit census.

LifetimeSafety retains all 202 remaining terminal names: 119 native or mixed
retypings and 83 retained contracts (79 product, four pure). Its 269-job scoped
build, all 202 named axiom checks, fresh kernel replay and complete independent
source review pass. The terminal module builds without warnings; its closure
still reports 704 inherited warnings. Arbitrary callbacks, full copied-world
trials and the original store-view premises remain. One changed-source forwarding
check failed before the corrected full-file check passed; no infrastructure
rerun was needed. The six earlier filesystem deletions are not counted again.

Configured-session support carries 18→17 theorems: thirteen native retypings,
four pure contracts retained, and the index-only replace_view frame deleted.
The actual adapter supplies its table-only write boundary inside tail_view;
the configured view observes peers, table rows and frontier, not the index.
Timer history retains all nineteen written theorem headers and adds four
private generic composition rules. Its deferred domain follows the current
fourteen-constructor source API; the removed raw-fire constructor is replaced
by wheel dispatch, not silently retained as a fifteenth case. Exact bucket
ordering, actual saved-map scans, missing-device/reset guards, end-of-wait
clocks, full product callbacks and failed journals remain in the source copy.
One new lookup adapter theorem carries the existing represented-tree total
lookup through the actual guarded AipStore adapter with both Ambient endpoints.

This checkpoint passes its 358-job scoped graph, 54 explicitly named axiom
checks, fresh replay of all three modules and independent source reviews.
ConfiguredSession and RxEnvTimersHistory build in 1.2 and 13 seconds with zero
module warnings; 1,305 warnings in the wider closure remain cleanup work.
ConfiguredSession had one ordinary failed development check before passing;
timer history passed its fourteenth changed-source check. No infrastructure
rerun occurred. A worker edit-driver syntax failure ran no tool; all dirty
worktrees were preserved at 20261017T005241Z before further edits.

RX carrier-state accounting retains all nine theorem names: seven native
retypings and two pure arithmetic contracts. The original seven-field store
mask and strict nonfinal-reference premise remain. Its 199-job scoped build,
all 22 named declaration axiom checks, fresh kernel replay and independent
source review pass. The module builds in 1.2 seconds with zero own warnings;
662 inherited warnings remain in its closure. The first output-free check
passed with one unused-simp warning; the corrected second check is warning-free.
No infrastructure rerun was needed.

Material retention carries 79→74 theorems: 41 native/view retypings, 29
retained product contracts, nine component-derived Skb-frame deletions and
four composition helpers. Arbitrary checksum, softirq, IRQ, reschedule and
Stack callbacks remain product actions. The 253-job scoped build, all 75 named
declaration axiom checks, fresh replay and complete independent source review
pass. The module builds in 109 seconds with zero own warnings; 983 inherited
warnings remain. Fifteen output-free development checks comprised thirteen
ordinary failures, one scoped-prefix pass and the final full-file pass.
Three edit-driver syntax failures executed no tool; no infrastructure rerun
was used.

The cleanup finding adds eighteen theorems and fifteen fixture definitions.
Its 200-job scoped build, all 33 named axiom checks, fresh replay and independent
source review pass; the module builds in 2.2 seconds with zero own warnings.
Four ordinary failed file checks preceded the fifth, warning-free pass.
The exact old selected-cleanup premises permit a last-reference peer with a
nonempty TX queue. Key payment returns, then peer payment stops at the queue
guard. This refutes the third conjunct of the historical
original_rx_cleanup_credit_discharge and four unrestricted totality helpers.
The unpublished fixture also satisfies QueueOwners. Normal-return preservation
and the stronger actual-ENOSPC contract are not refuted. These are counterexamples
to proof contracts over arbitrary local states, not initialized reachability
or Linux-bug claims. The [finding](2026-10-16-proof-state-split-findings.md#cleanup-totality)
records the declarations and reproduction commands. The four false helper exports are now withdrawn; terminal withdrawal and caller
repairs remain part of the unfinished R4 carry.

Stamped environment traffic retains all twelve original product theorem
headers and its four observer definitions. The source copy includes the current
IPv4 route/neighbour checks, native WG adapters, exact record-driven scheduling
and handshake-queue completion guards. Its 350-job build, all sixteen named
axiom checks, fresh replay and complete independent source review pass.
The module builds in 31 seconds with zero own warnings; 1,277 inherited warnings
remain. The final output-free traffic check passed; the combined timer/traffic
development ledger has nineteen changed-source checks (four passes, fifteen
failures) and nine isolated diagnostics (three passes, six failures).
No infrastructure rerun, cap increase or proof-limit change occurred.

Batch and environment-control history retain all twelve original product
contracts and four observer definitions, including arbitrary callbacks. The
batch observer follows the actual route, MTU and neighbour checks and native
WG/Ambient adapters; controls retain the existing fifteen-constructor domain.
The 368-job scoped build, sixteen named axiom checks, two fresh closure replays
and complete independent source review pass. Both modules have zero own
warnings; their closure still reports 1,283 inherited warnings. Two changed-source
batch checks were run: one failed, then the corrected source passed. No
infrastructure rerun, cap increase or proof-limit change occurred.

RX cleanup carries 26→25 theorems: twenty-one native contracts, four false
totality claims withdrawn, one type-derived freeRxSkb peer-view frame deleted,
and four separately named normal-return/nonfinal-payment contracts added.
These four withdrawals are included in the deletion total but are findings,
not consequences of the split's types. The thirty named declarations pass
standard-only axiom checks, fresh replay and complete independent source review.
The final source builds in 4.5 seconds without own warnings in the 401-job graph.
Twelve output-free development checks recorded eight ordinary failures, three
passes (two prefixes and one full candidate with a subsequently corrected binder
warning), and one missing-artifact failure. The final exact bytes passed the
central build after its dependency closure was restored; there was no redundant
output-free rerun. The stricter nonfinal theorem does not reuse the withdrawn
positive-credit theorem's name or claim.

Material lifecycle retains forty-two names, with thirty-eight native/state
contracts and four generalized StateT/project transports. Support history carries
35→36: two native receipt/execution retypings, twenty-four retained product
contracts, nine retained pure history facts and one private exact focus/lift
equality. Arbitrary product actions, the original store masks, strict positional
history prefixes and full saved probe Worlds remain in scope.

The combined import graph exposed independently generated socket helpers with
the same name. RxRingSocket now imports RoutingSocketFrames before elaborating
the common source; this acyclic import-only repair changes no contract. The
312-job lifecycle graph and final 352-job support graph pass, with zero own
warnings in the two carried modules. All 103 named declarations across those
modules and the socket repair have standard axioms only; all three fresh
closure replays and complete independent source reviews pass. The socket module's
eleven existing tactic deprecations remain warning-cleanup work.

Lifecycle development recorded six ordinary failed checks, one exit-zero
index-out-of-bounds panic (rejected), and one final pass. Support history's
first check failed on the generated-helper import collision; its final
warning-clean check passed after the graph repair. A separate axiom-driver
parse failure printed no roots; its corrected input passed all fifty roots.
Recovery snapshots include 20261017T010823Z for the panic, 010900Z for a root
driver syntax failure before tool execution, and 011410Z for the worker
serialization error following its failed import check. No limit was raised.

The receive-credit and syscall-history checkpoint carries 70→74 theorems:
fifty-three native/generalized contracts, seventeen retained shapes and four
private additions. No old theorem is deleted. Ingress retains all twenty-four
claims; its two new private lemmas derive nonfinal repayment from the actual
ENOSPC branch and existing queue/carrier funding. The original successful
key-put premise is unchanged. Thus this specialization survives the separate
unrestricted-totality counterexample. Protection retains all thirty-three
names, including arbitrary actual StateT/project instances for its generic
frames. TX packet frames remain substantive because the packet component can
also write the RX store.

Dispatch and syscall history retain all thirteen original product contracts.
The literal syscall observer now includes the current FIB-shape output suffix;
two private projection cuts separate entry from return-to-user work. Arbitrary
socket bodies and projected continuations keep their original domains.
Independent full source/contract reviews pass for all four modules. Central
builds pass (386 and 313 jobs); these modules emit no warnings, while their
closures report 1,325 and 1,285 inherited warnings respectively. All ninety-five
explicit named declarations have standard-only axioms, and all four fresh
kernel replays pass. These are scoped passes, not a full proof-gate pass.

Ingress worker checks recorded eight ordinary failures and two passes; the
root's earlier index-loan prefix also passed. Protection-frame development
recorded six ordinary failures and two passes. Dispatch/syscall development
recorded nine changed-source failures, two passes and three failed isolated
diagnostics before the final central pass. Three receive-layer axiom-driver
setup failures printed incomplete inventories; the corrected exact-Name
driver passed all seventy-six receive roots. No infrastructure retry or limit
change occurred in this checkpoint.

Material-support callers carry 40→39 theorems: six native leaves, one
saved-ring-item source-signature carry, thirty-one retained product contracts,
two deleted Ambient-only wrappers and one private native/product adapter.
The removed invariant/unsupported wrappers are replaced at actual callers
by the canonical Ambient lift; this follows their write boundary. Arbitrary
product callbacks and source_modify's exact forty-three-field premise remain.
Encryption now follows the actual ring consumption, NAPI work and saved-item
continuation. Independent source/contract review passes. The 365-job closure
builds; all forty named declarations have standard-only axioms and fresh
kernel replay passes. The module has zero warnings; its closure reports 1,389
inherited warnings. Development recorded six failed checks, one isolated
diagnostic pass and the final full pass, with no infrastructure retry, panic
or limit change.

Receive-runner history carries 27→31 theorems: all original product/pure
contracts and both trace/placeholder domains remain, with four private
composition helpers. Initialization, prefill, routing setup, copied probe
worlds and exact JSON/indexed Stops follow the actual runner. Its 390-job
closure builds with zero own warnings and 1,325 inherited warnings; all
forty-one named declarations have standard-only axioms and fresh kernel replay
passes. Five full changed-source checks and one isolated diagnostic failed
before the passing candidate. No success or trace-shape premise was added.

Transmit/receive protection carries 40→46 theorems: thirty-eight native or
generalized contracts, two retained product contracts and six helpers/bridges.
Arbitrary product actions remain available through projected transfer and
loan/repay contracts. The copied handshake queue continuation now consumes the
actual pending-work observation, as documented in the existing queue-bookkeeping
finding. The 318-job closure builds with zero own warnings and 1,338 inherited
warnings; all sixty named declarations have standard-only axioms and fresh
kernel replay passes. Complete source/contract reviews pass for both modules.
Transmit/receive development had six failed checks and six passing prefix/full
checks, one of the latter with two warnings subsequently corrected. No
infrastructure retry or proof-limit change occurred.

Material environment support carries 43→43 theorems: thirty-seven retained
product contracts, six deleted helpers and six current composition helpers.
Five deletions follow the removed raw timer scan/fire APIs; the sixth is the
global getter wrapper replaced at its actual call by the canonical product
read rule. Current wheel selection, duplicate saved-peer scans, completion
guards and delete callbacks retain their actual source behavior. The 384-job
closure builds with zero own warnings and 1,393 inherited warnings. All
forty-four named declarations have standard-only axioms; fresh kernel replay
and complete source/contract review pass. Development had two failed full
checks, one diagnostic pass and two full passes, without an infrastructure
retry, panic or limit change.

Receive consumption carries 73→76 theorems: all seventy-three original
contracts move to native or generalized actual-state carriers, with three
private conditional composition helpers. Receive key protection carries
59→56: fifty-four native/generalized contracts, five packet-component frames
deleted and two run-equivalence bridges added. The deleted frames observe no
packet-store field; their concrete callers use the canonical component adapter.
Nullable owner words, actual promotion, timer clocks, normal-return cuts and
the original seven-field store premise remain. Arbitrary product actions
remain available through the generalized StateT/project contracts.

The 319- and 320-job closures build without warnings in these two modules;
their wider closures report 1,338 inherited warnings. All 165 explicitly named
declarations have standard-only axioms, fresh replay passes and complete source
reviews pass. Consumption development recorded twelve ordinary failed checks
and seven passing prefix/full checks. Key protection recorded ten ordinary failed
checks and five passing prefix/full checks. No proof limit or cap changed.
Consumption's first fresh replay returned no completion status and is recorded
as an infrastructure failure; its sole rerun returned an explicit zero status.

Material configuration and dump retain all twenty-five names: twenty-three
native contracts and two generalized actual-state transports. They preserve
the original allocation/dump observations and seven-field store mask, including
negative errno returns and partial updates. Their 317- and 330-job closures
build with zero own warnings; all twenty-five named declarations have standard
axioms only and fresh replay and complete source review pass. Configuration
development had three ordinary failures followed by a pass. Dump's first check
failed before reaching its body because two imported proofs generated the same
cryptAhead matcher helper; removing an unused import let its second check pass.
The combined graph collision still requires its separate proof-body repair.

Remaining work is the routing/origin terminal carry, material runner support,
RX stack/carrier layers, the combined import repair, warning
cleanup, the full proof gate and terminal replay. Deterministic source/proof
failures are failures; source edits are checked anew, never described as
infrastructure retries. Recovery admissions printed by failed elaborations
were rejected. No memory cap or proof limit was raised.

Each infrastructure rerun below occurred once for its affected invocation:

| Invocation | Infrastructure failure | Single rerun outcome |
| --- | --- | --- |
| Initial unit suite | stale executable; eleven failing tests | PASS after executable rebuild |
| RoutingHistory axiom check | missing PrefixState artifact | PASS after dependency repair |
| RoutingHistory fresh replay | missing PrefixState artifact | PASS after dependency repair |
| TX ring witness | imported cut artifact absent during rebuild | FAIL on tuple typing; only later changed-source proof passed |
| BatchCalls range diagnostic | invalidated dependency | FAIL on proof/type inference |
| RxOriginCuts cleanup build | missing artifact during concurrent writer | PASS after writer completion |
| RxPhase diagnostic | missing shared artifact | FAIL at unchanged heartbeat limit |
| SyscallsAudit diagnostic | missing shared artifact | FAIL on proof obligations |
| RunnerSafety diagnostic31 | EnvTimersAudit artifact absent during central rebuild | PASS unchanged after rebuild |
| RxConsumeProtection fresh replay | tool returned no completion status; handle subsequently absent | PASS with explicit zero status |

Explicitly stopped elaborations, signal/KILLED outcomes, driver crashes and
toolchain panics were preserved to snapshot refs before work resumed; they
never count as passes. Stops targeted only verified owned PIDs. An accidental
unscoped `leanchecker --help` invocation was KILLED at 32G with exit137 and was
not rerun. Subsequent replay commands name their module explicitly.
Runner composition diagnostics also exposed a no-progress matcher that repeatedly
split only the first discriminator. The canonical targeted match splitter fixed
it without changing statements or limits. Superseded diagnostics were explicitly
stopped (exit143/KILLED); a diagnostic-only same-module IO.Ref initialization
crashed with exit134. These are failures. All dirty worktrees were preserved,
including snapshots at 20261017T001124Z and 20261017T001204Z, before further work.
One central Lake writer now coordinates this worktree's artifact mutations; independent
checks and work in other worktrees remain concurrent.

## Runtime witnesses still needing reconstruction

The existing witness programs compile. Each recipe below was run once, with
no infrastructure rerun:

| Recipe | Current runtime result |
| --- | --- |
| r2-stale-dump-cursor | PASS |
| r2-stale-dump-cursor-orphan | PASS |
| r4-gro-reorder | PASS, exact ciphertext order |
| r6-retransmit-limit | FAIL at operation 2: expected timer clock site 428, saw 41 |
| r5-delayed-encryption | FAIL at operation 1: expected site 428, saw 8 |
| r5-coherent-post-clear | FAIL at operation 1: expected site 428, saw 8 |
| r5-post-clear-transport | FAIL at operation 4: no modeled timer bucket due at jiffies 135005 |

All four failures precede the proof observers. The historical generator uses
an older roaming seed and synthesizes timer inputs without the current wheel
clock records. These exact recipes still need reconstruction; a different
passing fixture would not establish them. The mirror and generator were
unchanged at this checkpoint. These failures are not guest timeouts or passes.

## Reproduction

~~~sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
export LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16
cap scripts/in-bundle lake build LeanuxProofs
cap scripts/in-bundle scripts/proof-gate
# Recheck a particular completed module:
cap scripts/in-bundle lake env leanchecker --fresh MODULE
~~~

The full build/gate commands above describe the remaining claim-point checks,
not a recorded full pass. For a runtime recipe, substitute CASE and MODULE:

~~~sh
cap scripts/in-bundle bash -o pipefail -c \
  'python3 -B docs/proof-campaign-replay.py CASE | lake env lean --run Leanux/Proofs/WG/MODULE.lean'
~~~

The module mapping is LifetimeSafety/Replay and ReplayOrphan for the two R2
recipes, DeliveryOrder/ReplayGro for R4, FloodResistance/Replay for R6,
KeyLifetime/ReplayDelayed for delayed/coherent R5, and
KeyLifetime/ReplayPostClear for post-clear transport.
