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
replay. Older
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
