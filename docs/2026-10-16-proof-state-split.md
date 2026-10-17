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
| Current retrofit source | 452 | 6,558 |

The complete source census comprises **3,197 retyped/generalized, 1,709 deleted,
2,809 retained contract shapes and 552 added theorems**. Retyping changes the
actual carrier or observation, including shorthand contracts whose functions
move to a native monad. Namespace-only product qualification and equivalent
projection relocation count as retained. The census includes private and
attributed declarations and excludes nested comments, strings and tactic-local
variables. These totals include the validated stable-receive and R4 carries below.

Independent reconciliation adds 437 previously unclassified retained claims:
286 byte-identical declarations and 151 with proof-only warning repairs. Of
these, 420 are pure and seventeen retain product/history scope. It also removes
seven duplicate retained Enqueue entries: their original carry was counted in
both `4c8a99b` and `02fa172`. The latter checkpoint's corrected subtotal is
84 old, forty retyped, three deleted, 41 retained and eleven added, yielding 92.
Thus the baseline is 3,197 + 2,809 + 1,709 = 7,715; the current source is
3,197 + 2,809 + 552 = 6,558. No unexplained residual remains.

The terminal surface has 517 declarations: 515 theorems and two definitions.
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

The unchanged mirror passed its model build (66 jobs), executable build
(130 jobs) and unit suite (131 tests, one skip). Completed proof checkpoints
have scoped builds, named-declaration axiom checks, explicit fresh kernel
replay and independent source reviews. None establishes a full-tree pass.

The carried LifetimeSafety terminal has 202 declarations: 119 native/mixed
retypes and 83 retained contracts. CryptokeyRouting retains all 141 names:
110 retyped/generalized and 31 retained (twenty pure, eleven product).
Their scoped builds, every named axiom check, fresh replay and complete
reviews pass. The terminal modules have zero own warnings.

CryptokeyRouting removes three compound clauses with source justification:
the index-only operation's routing frame, the Seccomp/Task-only prefill
initialization clause and the removed fireTimer API's clause. Actual wheel
dispatch, the original initialization mask and arbitrary product callbacks
remain. This is a carry of existing statements; initialized packet
authorization remains open.

Receive admission, cleanup, ring ownership, stack/GRO transfer, publication
identity, receipt links, completion and outer history composition have been
carried. Native receipts preserve both WG and Ambient endpoints; mixed
callers retain arbitrary product actions, all trace/flag domains, exact
Stops and full failure journals. Ingress preserves its existing normal-run
premise and uses the successful cleanup receipt, without reinstating the
refuted totality claims.

Stable receive retains all 39 theorems: 35 native retypes, one arbitrary-state
generalization, two pure contracts and its product physical-journal contract.
Its 45 named logical declarations pass axiom inspection. DeliveryOrder moves
from 129 to 131 theorems: 32 retyped, 96 retained, one false compound withdrawn
and three separate supported-cuts, counterexample and normal-cleanup exports.
The final combined 431-job build, all 131 R4 axiom checks, fresh kernel replay
covering both modules and WGData, and independent reviews pass. Each changed
module has zero own warnings; the complete dependency build reports 1,200.
Stable receive had five failed development checks and two passes. R4 had nine
passes, two ordinary failures and one infrastructure failure, whose sole
unchanged rerun passed. A preliminary Stable replay passed before WGData was
rebuilt; the final R4 replay checks their combined final dependency closure.

WGData's two unchanged contracts use direct Ambient composition and the exact
normal-run bridge. Its two named axiom checks and independent review pass;
the final R4 replay covers this repair. Three drafts failed on source joins,
branch selection and the unchanged 200,000-heartbeat limit before the fourth
passed. No failure was relabeled as a successful check.

Remaining work is compiler-warning cleanup, the full proof gate and terminal
replay. The first complete gate failed at the root import: independently
compiled Operations and RoutingEnvTimersFrames exported the same generated
`requireNothingDue` matcher declaration. Its other source checks passed, but
the invocation remains **FAIL**; it reported 859 warnings and did not inspect
the terminal axioms. The repair replaces the two offending proof bodies with
direct execution cases and preserves all 22 module contracts. Both complete
candidate checks pass and confirm the conflicting generated declaration is
absent. Development had seven ordinary failures, one infrastructure failure
and three passes; the sole infrastructure rerun failed on proof obligations
before the source was repaired. The second complete gate also failed: its
three import errors exposed generated matcher collisions for `enqueuePerPeerTx`
and `lookup`. It reported 451 warnings; source checks passed and terminal axiom
inspection was skipped. The enqueue repair passes its complete source check,
all seven named axiom prints and an assertion that the conflicting declaration
is absent. Its first two drafts failed on parsing and predicate normalization.
Independent review's trailing-whitespace finding was corrected after the
active build. That 182-job scoped build failed at an upstream `keypairGet`
matcher collision between Ordinary and RxHelperFrames; it reported 41 warnings.
The three Ordinary proof replacements pass without warnings, all eighteen
logical roots have standard-only axioms, and the conflicting declaration is
absent. The next 205-job import build also failed: RxHelperFrames and
AllocationReleaseFrames still independently generated that helper. It reported
83 warnings. Both repairs now pass their complete source checks, with unchanged
theorem contracts and standard-only axioms; both conflicting declarations are
absent in their source checks. The 297-job combined import build still failed:
RoutingTxFrames imported a duplicate enqueue matcher from RxTxFrames and
TxRingFrames. It reported 320 warnings; the targeted RxTx, receive completion,
ring callback and two scheduler modules built, but the invocation is **FAIL**.
All remaining RxTx deprecated proofs now pass their source and seven axiom
checks without warnings, and the source check confirms the helper is absent.
Independent review preserves saved peer receipts, physical ring semantics,
partial Stops and the original surviving-resident relation. The next 285-job
combined build failed at RoutingTxFrames: RoutingSendFrames and TxRingFrames
still generated the enqueue helper independently. It reported 291 warnings;
the changed RX/TX, completion, packet ECN, product syscall and runner modules
built. Fresh replay of runner bounds, product syscall frames and receive
completion passes.
Runner uniqueness and window-bound proofs share checked
Triple composition over the actual runner. All eleven theorem contracts and
three pure definitions remain unchanged, including arbitrary syscall contracts,
initialization, indexed Stops and both placeholder settings.
The routing enqueue repair preserves all nineteen module contracts and passes
its standard-axiom and generated-helper absence checks; twelve older tactic
sites remain. Independent source review passes. A separate output-free
refcount diagnostic failed because a generic WG action is not definitionally
equal to the proposed native Ambient lift; no source was published from it.
No complete gate or root replay is claimed yet. Older
proof modules still use deprecated automation or redundant simplifiers.
Lean 4.35's vcgen is a different implementation from mvcgen; blind renaming
does not preserve these proofs. Nine foundation/logged warning repairs preserve
all eighty theorem contracts and options. Their 69-job build, 105 named logical
declaration axiom checks, four fresh replays covering all nine modules and
independent source review pass. All nine modules have zero own warnings; their
closure retains nine warnings. Two Hoare proof drafts failed before the final
direct proof passed. Keypair base and encryption warning repairs preserve all
120 contracts: both modules build without warnings, all 120 named axiom checks,
fresh replays and independent reviews pass. Their wider 284-job invocation
failed in Logged/Operations after a deprecated string-constructor replacement;
the repaired pure-return agreement passes its 50-job build, 24 named axiom
checks, fresh replay and independent source review, with zero own warnings.
Seventeen other modules built in that invocation and contain only equivalent
conditional-theorem name replacements; independent review confirms all 41
replacements and unchanged contracts. The wider invocation remains a failure.
Encryption development
had three failures (including the unchanged two-million-heartbeat limit) before
its direct proof passed; keypair base had two failures before two passes.
No theorem counts change in this maintenance.

The timer observer and three native time/Noise/index frame modules preserve
all 48 contracts. Their combined 348-job dependency build, 59 named logical
axiom checks, three scoped fresh replays and independent reviews pass, with
zero warnings in the four modules and 1,109 warnings in the complete closure.
The timer observer's four failed development checks included 23 heartbeat
timeouts, a parser error, a tactic quotation defect and an unhandled throw
head. Passing the actual Ambient operand to its checked lift rule removes the
expensive inference. The final check passes at the original limits. The small
Noise and index repairs each had one failed draft before passing; time passed
its first check. None changes a statement or the executable mirror.

The next maintenance batch removes 465 reported unused simplifier arguments
from 92 modules; all 95 candidate checks pass and independent review confirms
unchanged contracts and options. Formatting findings were corrected before
publication. Seven further candidates remove eighteen unused arguments and
three other diagnostics; all seven checks and reviews pass. The intentionally
unused `stamp` premise is retained with the binder renamed `_stamp`.

Native socket, cookie, device, allowed-IP and dump proofs now compose checked
source actions directly. Product environment proofs retain the original
43-field observation and actual mixed actions. The transition helper shares
existing ordinary-composition support by moving one private meta helper and
four elaborators unchanged into OrdinaryRules. The final combined 237-job
build passes, including WGTransitions, WGMore and WGConfig; its dependency
closure still reports 187 warnings. This is a scoped pass, not a root pass.

| Additional maintenance checks | Ordinary failures | Passes |
| --- | ---: | ---: |
| Socket, Product and Batch | 6 | 3 |
| Environment leaves and allowed-IP helpers | 4 | 3 |
| Device lifecycle, cookie and header frames | 10 | 3 |
| Environment operations and syscall frames, including source axiom prints | 7 | 4 |
| Shared transition support and configuration consumers | 15 | 5 |
| Receive snapshot composition | 3 | 1 |
| Dump frames | 0 | 1 |
| Device snapshot frames | 1 | 1 |
| Product environment snapshot frames | 3 | 2 |
| Peer borrowing and repayment | 5 | 3 |
| WP and hot-path keypair contracts, including twelve source axiom prints | 7 | 4 |
| Enqueue collision, including seven source axiom prints | 2 | 2 |
| Remaining operation completion frame | 0 | 1 |
| Ordinary keypair contracts, including eighteen source axiom prints | 3 | 2 |
| Exact TX enqueue result | 2 | 1 |
| Receive-queue primitive frames | 1 | 1 |
| TX/RX ring admission guards | 0 | 1 |
| Receive queue helper frames, including eight source axiom prints | 6 | 2 |
| Lookup borrowing and wrappers, including twenty-five source axiom prints | 6 | 2 |
| Scheduler pending-NAPI frame | 0 | 1 |
| Receive maintenance and timer queue frames | 4 | 2 |
| Product encryption scheduler frame | 1 | 1 |
| Product syscall wrappers, including ten source axiom prints | 1 | 2 |
| Remaining TX queue frames, including seven source axiom prints | 3 | 2 |
| Receive completion frames, including five source axiom prints | 1 | 2 |
| TX packet ECN frame | 2 | 2 |
| Runner uniqueness/window-bound composition, including fourteen source axiom prints | 1 | 3 |
| Routing enqueue collision, including axiom and helper-absence checks | 1 | 1 |

Earlier transition passes retained two deprecated bodies; only its final three
passes validate the complete replacement and relocation. Peer borrowing's first
pass retained nineteen unused arguments; both subsequent checks have zero
warnings. All these repairs retain theorem contracts and existing proof limits.
Receive maintenance had an intermediate pass retaining three deprecated blocks;
its final pass is warning-free. Product encryption retains the arbitrary
product-state checksum callback and its original premise.
WP retains the saved keypair facts across both owner/index removals and the
original allocation-frontier premise; its final check has zero warnings.
The two unused frame macros are removed after all callers were replaced;
their ten logical contracts remain, and the module checks without warnings.
The exact enqueue result keeps peer refusal before the ring-full test and
does not treat a queue-work Stop as an ordinary return. The queue primitive
and Ordinary replacements retain all contracts; independent reviews pass.
The environment/admission checkpoint passes its combined 171-job build, with
27 warnings in the dependency closure. Both scoped fresh kernel replays
(environment frames and enqueue admission) pass with explicit zero status.
Named failures include compiler-join normalization, action inference, ordinary
heartbeat exhaustion and malformed drafts; none was treated as a pass or an
infrastructure retry. The final candidates received independent source review. Receive completion
and TX ECN each had one intermediate pass retaining two warnings; their final
passes have zero own warnings. Explicit branch reduction and source operands
resolved the TX ECN inference timeout without raising its existing limit.

Deterministic development failures, including generated-helper import
collisions and heartbeat exhaustion, are failures. Changed source was
checked anew; these were not infrastructure retries. Recovery admissions
printed by failed elaborations were rejected. No memory cap or proof limit
was raised. The encryption import collision was repaired in two proof
bodies while preserving all sixteen contracts; the complete R3 source,
central build, axiom checks and replay then passed.

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
| RxPollDisposition diagnostic | missing Completion artifact | FAIL on proof obligations; changed-source checks later passed |
| DeliveryOrder diagnostic | RxRingHandshake artifact absent during central rebuild | PASS unchanged after rebuild, first 109 declarations |
| Operations collision repair | WGBase artifact absent during the warning-composition build | FAIL on proof obligations; changed-source checks later passed |
| Routing timer warning repair | RoutingTxFrames artifact absent after the failed full build | Pending dependency repair; no rerun yet |

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
Three read-only comparison-driver mistakes (a Python index error, an
overbroad binder-name comparison, and a JavaScript method typo) were failures,
not Lean results. Dirty worktrees were preserved at 20261017T033106Z,
20261017T033734Z and 20261017T034000Z before continuing; branch tips remained
unchanged. The corrected contract census still reports 452 files and 6,558
theorems. These checks did not publish partially validated source.
An ephemeral lookup-report driver later failed on a Python boolean literal
after the Lean check had passed. Four dirty worktrees were preserved under
`refs/snapshots/proof-campaign-lookup-ledger-recovery-20261017T040418Z/`
(campaign `b798306d7cef9a951def0555089eb9c933e3e975`). The failure changed no
tracked source and is separate from the Lean validation; branch tips stayed put.

## Runtime witness reconstruction

The existing witness programs compile. Each old recipe below was run once,
with no infrastructure rerun:

| Recipe | Current runtime result |
| --- | --- |
| r2-stale-dump-cursor | PASS |
| r2-stale-dump-cursor-orphan | PASS |
| r4-gro-reorder | PASS, exact ciphertext order |
| r6-retransmit-limit | FAIL at operation 2: expected timer clock site 428, saw 41 |
| r5-delayed-encryption | FAIL at operation 1: expected site 428, saw 8 |
| r5-coherent-post-clear | FAIL at operation 1: expected site 428, saw 8 |
| r5-post-clear-transport | FAIL at operation 4: no modeled timer bucket due at jiffies 135005 |

All four failures preceded the proof observers and remain failures. The three
arm-enabled recipes now generate the wheel's base-clock and enqueue records,
including its distinct same-expiry and same-slot paths. Their recorded timer
units follow the actual detach/cancel operations. The mirror validates every
generated record; these synthetic inputs are not Linux captures.

[AGENT 2026-10-17] Reconstruct the same post-clear behaviors using the actual
wheel firing windows. The coherent variant moves encryption from 673 to 679
seconds and ends at 680 seconds: its zero-key bucket becomes due at 678.832.
The legacy 25-second recipe cannot preserve its five-unit schedule because
post-transmit rearming is already due. Its replacement uses a 535-second
keepalive and wait endpoints 1000, 1001, 2000, 139263, 139264; persistence runs
before zero-key in their shared bucket and rearms beyond the final wait.
Only the corresponding numeric runtime assertions change. The exact retained
key, nonce, ciphertext, reference counts, callback order and erasure checks remain.

Each of the four changed recipes passes its first runtime run with zero
warnings, no infrastructure rerun and all original/observer comparisons intact.
R6 still has nineteen retry callbacks, twenty initiations total and give-up on
callback twenty. The three R5 cases retain lifetime 1 and wire nonce 1, with
identical ciphertext. Independent source review passes. No theorem or mirror
behavior changed, and the old fixtures are not presented as passing unchanged.

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
