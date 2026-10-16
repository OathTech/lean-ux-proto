# Proof campaign: state-split retrofit

The branch `proofs/campaign` carries split mirror `6089dc4`, merged at `6e0a5c8`.
The executable mirror is unchanged by the proof work. The nondefault
`LeanuxProofs` target and `scripts/proof-gate` remain on this branch. The
[split design](2026-10-15-design-state-split.md) describes the new worlds and
monads; further R3/R4 results follow the retrofit.

## Counts and status

The validated pre-split baseline is `00641c6`: 471 tracked Lean files under
`Leanux/Proofs/`, 7,715 named theorem declarations, and 521 terminal declarations
(519 theorems and two definitions). The theorem census strips nested comments
and strings and includes private and attributed declarations. The uncommitted
configured-closure extension was preserved before resumption and is deferred;
it is not part of that baseline.

| Completed proof change | Before | Retyped | Deleted | Retained contract shape | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| CounterWindow `Refinement`, `MirrorCalls`, `Bounds` | 31 | 17 | 6 | 8 | 1 | 26 |
| Framing `Basic`, `WP`, `Allocation`, `Index`, new `Hoare`/`Lift` | 40 | 25 | 14 | 1 | 14 | 40 |
| Logged `Basic`, `Outer`, new `Ghost` | 27 | 14 | 0 | 13 | 4 | 31 |
| Lifetimes `Actions`, Framing `Projection`, `Tools` | 21 | 19 | 2 | 0 | 4 | 23 |
| Logged prefix core (11 files), new `PrefixState`, `WGPrefix`, `NativeCapture` | 128 | 113 | 0 | 15 | 44 | 172 |
| Keypairs `Lifetimes`, `LifetimeMirror`, `Identity` | 34 | 8 | 4 | 22 | 0 | 30 |
| Obsolete subsystem-frame band (26 modules) | 1,427 | 0 | 1,427 | 0 | 0 | 0 |
| Unused `Framing.Control` support | 6 | 0 | 6 | 0 | 0 | 0 |
| Obsolete `Framing.Prefill` and unused support | 3 | 0 | 3 | 0 | 0 | 0 |
| Keypairs `Ordinary` | 17 | 12 | 1 | 4 | 0 | 16 |
| Framing `WGTime`, `WGHandshake`, Keypairs `OrdinaryHot` | 21 | 16 | 5 | 0 | 0 | 16 |
| WG store view and Keypairs composition (four modules) | 31 | 27 | 4 | 0 | 0 | 27 |
| Logged `RxPoll`, `Tools`, `Workers`, `Scheduler` | 26 | 0 | 0 | 26 | 0 | 26 |
| Index table, trie-removal source, receive headers and data helpers | 12 | 8 | 4 | 0 | 0 | 8 |
| Component adapter extension (new contracts only) | 0 | 0 | 0 | 0 | 7 | 7 |
| Native socket/configuration frames and new WG-owned view | 9 | 9 | 0 | 0 | 0 | 9 |
| Product evolution rules and new ordinary lift bridge | 24 | 0 | 0 | 24 | 1 | 25 |
| Native WGBase contracts and generalized map rule | 185 | 117 | 68 | 0 | 0 | 117 |
| Redundant filesystem-family wrappers and exports | 21 | 0 | 21 | 0 | 0 | 0 |

The whole tree currently contains 449 Lean files and 6,225 theorems. The completed
changes total 385 retyped theorems, 1,565 deletions, 113 retained contract shapes and 75 added.
Retyping changes or generalizes the actual state/monad carrier or observation.
This includes shorthand contracts whose source functions or named views move
to a native monad. Mere namespace qualification and equivalent relocation of a
product-state projection count as retained contract shapes; their proofs and
source observers may still require substantial repairs. All carried contracts
use the actual new stack.

The count audit corrects the scheduler row from 17 retyped / 9 retained to
0 / 26: those seventeen signature edits qualify the same product monad as
`Leanux.M`. The earlier description in terms of unchanged written signatures
was inconsistent with the native source-equality and acceptance-observer rows.
Before this checkpoint, the corrected totals are 259 retyped / 89 retained,
rather than 276 / 72. The before/after, deletion and addition counts are unchanged.
Six terminal files remain unchanged. LifetimeSafety loses six redundant filesystem
exports; every retained terminal body is unchanged. The terminal surface is now
515 declarations (513 theorems and two definitions). **Every result remains lagging** until the complete tree
passes its proof gate and kernel replay. R1/R2/R5/R6 retain their pre-split
charter dispositions; initialized R3 packet authorization and R4 receive-pipeline
conservation remain open.

## Counter-window port

Record updates now take `Ambient`; the keypair store and counter projection take
`WGWorld`. Exact execution states both inputs and both successful outputs:
`((action.run wg).run ambient) = .ok ((value, wg'), ambient')`. The call-list
induction threads each actual outgoing ambient into the next call. Device,
keypair and 128-word bitmap premises, exact records and operands, acceptance,
update, uniqueness and bounds are retained.

Deleted: `clearRecords_k`, `record_k`, `recordCmp_k`, `record_counterAt`,
`recordCmp_counterAt` and `clearRecords_counterAt`. Their old cross-state
expressions disappear when recording has only ambient state. This is a type
justification, not a failed-compilation justification. The one new private
lemma states the generic StateT/list-iteration lifting law needed by the exact
loop equation. No compatibility world or execution wrapper was introduced.

Validation: scoped build passes (33 jobs); all 25 public theorem axiom prints
use only the permitted axioms, including transitive coverage of the private
lemma; fresh kernel replay passes. Independent frozen-source review compared
every changed statement and the actual mirror operations and found no
substantive issue. Scope/hash/prohibited-construct checks and the scoped diff
whitespace check pass. Three earlier scoped builds failed on conversion
plumbing. The first emitted three rejected elaboration-recovery `sorry`
diagnostics; no source admission was introduced, and the successful checks
contain none. No interruption, cap increase, proof-limit increase or
infrastructure retry occurred in this port.

Reproduce the scoped compilation and kernel replay with:

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.CounterWindow.Bounds
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.CounterWindow.Bounds
```

## Native contracts and adapters

`Hoare` and its composition rules now apply to the actual `StateT` stack.
The native run bridges quantify ambient and task endpoints explicitly; total
contracts still require a successful execution. Exact subsystem lift equations
retain every Stop, including the index adapter's missing-device guard before
the table action. Allocation and index source equations remain definitional.
The keypair counter, owner-read and allocation/deletion contracts retain their
substantive content. `branch_wp` retains its Boolean-return claim in `AmbientM`.

The 14 deletions comprise six obsolete Kernel API facts, seven ambient-only
Kernel frames and the index-unhash counter frame. The latter follows from the
single index adapter rule and explicit stability of the counter projection.
No return, totality or exact-error claim was deleted. One exception rule moved
unchanged; 14 shared execution/adapter lemmas were added. No replacement Kernel
or flattened execution world was introduced.

Validation: final scoped build passes (37 jobs), all 47 declarations print only
permitted axioms, and fresh scoped kernel replay passes. Independent frozen-source
review found no substantive issue. Source hashes, terminal-file preservation,
mirror equality to `6089dc4`, prohibited constructs and scoped whitespace pass.
Eight earlier builds failed on elaboration/conversion work; one displayed a
recovery goal containing `P sorry`, with no source admission and no nonstandard
axiom in the successful validation.

An operational mistake ran `leanchecker --help` uncapped. It started an unscoped
replay, reported a problem in the unported `Framing.WGSocketLifecycle` module,
and was stopped using only its inspected owned PIDs (exit 143). This was a
failure, not validation. Every dirty worktree, including untracked source, was
snapshotted before work resumed, with branches and normal indices unchanged.
The subsequent capped scoped replay passed. No timeout, KILLED outcome, cap
increase or infrastructure rerun occurred in this tranche.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.Framing.WP Leanux.Proofs.Framing.Lift
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Framing.WP
```

## Native acceptance observations

`Ghost` holds the ten existing generic erasure proofs, moved byte-for-byte from
`Outer`. `Basic` reuses them, generalizes 11 theorems and retypes the three counter
contracts over `WGWorld` and `Ambient`. Three helper/product interfaces remain.
The counter observer still runs the actual validator once and appends exactly
one lifetime/nonce event only on acceptance, retaining both outgoing states.
Missing-device and missing-key failures remain exact. Four new extraction/lift
lemmas connect generic erasure to native and product execution through actual
`liftWG`. The outer runner still attaches exactly its operation index to Stop.
This success-only observer retains no history on failure; the separate Prefix
layer must continue to retain failure history.

Validation: final scoped build passes (34 jobs), all 89 module-owned declarations
(43 explicit source declarations) print only permitted axioms, and fresh scoped
kernel replay passes after compilation. Independent frozen-source review found
no substantive issue. Hash, source-token, mirror, terminal-preservation and
whitespace checks pass. Two earlier builds failed on normalization and one
parser typo; there was no admission, recovery admission, interruption, timeout,
KILLED outcome, limit increase or infrastructure rerun.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.Logged.Outer
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Logged.Outer
```

## Native actions and projections

`Action`, `ProjectedAction`, `SameView` and the finite-loop/map/discard rules now
use the actual generic `StateT` stack. Four exact run bridges retain every native
input and successful output. `Executions` passes each call's returned subsystem
state and Ambient directly into the next call. These partial contracts observe
the outer state; predicates depending on Ambient still require a multistate
contract. No successful-run, failure or progress premise was discarded.

The two deleted theorems, `Action.of_sameKernel` and `SameView.of_sameKernel`,
transported through the removed Kernel projection. Separately, the `frame_wg`
tactic macro hard-coded that old interface and is deleted; its remaining callers
are still lagging. `pinned_const` is retained. These macro changes are outside
the theorem counts.

Validation: scoped build passes (14 jobs), all 28 explicitly named declarations
print only permitted axioms, and fresh scoped kernel replay passes. Independent
review compared the complete claim diff and the three execution-chain consumers
and found no substantive issue. Hashes, source-token scan, terminal preservation,
mirror equality and scoped whitespace pass. Two earlier builds failed on implicit
state variables and function extensionality. No admission, recovery admission,
interruption, timeout, KILLED outcome, limit increase or infrastructure rerun
occurred.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.Framing.Tools
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Framing.Tools
```

## Failure-prefix contracts and native receipts

The eleven existing prefix modules now work over an arbitrary actual state.
All 128 theorem names and their content remain: 113 signatures are generalized;
15 pure or outer-runner signatures are unchanged. The new nested-StateT rules
pass both returned native states and the journal into each continuation. A Stop
retains the reached journal and exact exception, without inventing failed state
endpoints. The 44 added theorems cover this composition, the real WG-to-product
adapter, and native capture.

Native receipts retain before/after WG and Ambient states. Successful observed
capture retains the actual incoming-history witness and exact nested execution;
it executes the observer once. Failed capture keeps its outgoing journal, and
only success appends a receipt. The product `PrefixM` and `RunWitness` aliases
continue to describe actual runner executions. No reconstructed monolithic
execution state or historical-event translation was introduced.

Validation: the final scoped build passes (54 jobs), all 221 named declarations
print only permitted axioms, and four fresh scoped replays cover all fourteen
files. Independent frozen-source review found no substantive issue and confirmed
the counts. Source hashes, prohibited-token scan, terminal preservation, mirror
equality and whitespace pass. Thirteen earlier builds failed on polymorphic
binders, tuple/alias normalization and namespace resolution. No source or recovery
admission, interruption, timeout, KILLED outcome, limit increase or infrastructure
rerun occurred. All four replay handles completed successfully.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.Logged.NativeCapture Leanux.Proofs.Logged.PrefixOuter Leanux.Proofs.Logged.PrefixControl Leanux.Proofs.Logged.ProjectsUnderTo
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Logged.NativeCapture
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Logged.PrefixOuter
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Logged.PrefixControl
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Logged.ProjectsUnderTo
```

## Native keypair snapshots and identities

The lifetime snapshot now takes `WGWorld`. Validator evolution and preservation
use actual WG and Ambient inputs and successful outputs, preserving exact
acceptance history and false-return bitmap updates. The getter retains equality
of both returned states and the current-slot lifetime fact. The pure lifetime
algebra is unchanged. The canonical initial snapshot describes the actual
`Runner.initialWG net bare`; the old task/file/seccomp initialization wrapper
collapses to this same conclusion.

Three recording frames are deleted because their operations now take only
Ambient, outside the WG snapshot. The fourth deletion is the redundant
initialization wrapper. No boundedness or reachability premise was added.

Validation: final scoped build passes (77 jobs), all 43 named declarations print
only permitted axioms, and fresh Identity kernel replay passes. Independent
frozen-source review found no substantive issue. Hashes, prohibited-token scan,
terminal preservation, mirror equality and whitespace pass. One earlier build
failed on elimination of two impossible native failure equations. There were five
capped calls, no admission, interruption, timeout, KILLED outcome, limit increase
or infrastructure rerun; all handles are collected.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Keypairs.Identity
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Keypairs.Identity
```

## Removed subsystem-frame layers

The new subsystem monads cannot access the old global Kernel. The independently
audited 26-module band contains 1,388 obsolete structural/transport facts and
39 support theorems used only within that band. Those support facts include
arithmetic, progress and arbitrary-callback composition: they are deleted as
unused, not claimed to follow from subsystem separation. Six more unused
theorems and their tactics are removed with `Framing.Control`. `Framing.Prefill`
loses its obsolete cross-subsystem theorem and two unused private helpers.
Thus this checkpoint removes 1,436 theorems: 1,389 obsolete facts and 47 unused
support facts.

Removed modules:

- `Framing/{Eventpoll,EventpollCalls,FS,FSBase,FSFileRefs,Kernel,KernelEffects,Pipe,PipeAux,PipeRead,Seccomp,SeccompBridge,SeccompFilter,SeccompU,Signal,Wait}`.
- `WG/Keypairs/Frames/{Eventpoll,EventpollCalls,FS,FSBase,Kernel,Pipe,PipeAux,PipeRead,Seccomp,Wait}`.
- `Framing/{Control,Prefill}`.

Only their 32 import edges are removed from 30 surviving files; those files'
proof bodies and all terminal statements are unchanged. Their remaining native
and product obligations still need carrying. In particular, initialized runner
conclusions must use the actual `initialWG` construction: a seccomp/task prefill
premise alone cannot imply an empty WG snapshot of an arbitrary product World.
Conditional projection transport and within-WG preservation remain substantive.

The 224 named generated artifacts of the deleted modules were removed from this
worktree's private build tree. All previously ported targets still build together
(97 jobs). Source/import scope, terminal preservation and whitespace checks pass.
Independent frozen-source review confirmed the 28-file, 1,436-theorem deletion,
its classification and all 32 import removals, with no substantive findings.
No named generated artifact remains for these modules. No new theorem was
introduced, and no full-tree pass is claimed.

## Native ordinary lifetime actions

`OrdinaryAction` and `SameSnapshot` now use the generic projection contracts over
actual `WG.M` executions. Their run bridges quantify every incoming and outgoing
WG and Ambient state. Stable-predicate characterization, composition, getter
preservation and allocation/deletion behavior retain their arbitrary-state scope.
Both owner reads and unhashes remain in keypair release, including the actual
missing-device and record failure paths. No boundedness, reachability or
allocation-success premise was added. Four pure map theorems are unchanged;
the only deletion transports through the removed Kernel projection.

Validation: frozen build passes (80 jobs), all 20 named declarations print only
permitted axioms, and fresh scoped kernel replay passes. Independent frozen-source
review confirms all 17-to-16 theorem dispositions with no substantive findings.
Hashes, source scan, terminal preservation, mirror equality and whitespace pass.
Six development builds failed; one hit the existing 200,000-heartbeat limit and
one attempted an incompatible tactic deprecation cleanup, which was reverted.
The bounded proof now passes without a limit increase. No process was interrupted:
the long-running build had exited before its PID was rechecked. A conservative
snapshot nevertheless preserved all dirty worktrees, including untracked files,
with branches and normal indices unchanged. All ten capped-call handles are
collected; there was no KILLED outcome or infrastructure rerun.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Keypairs.Ordinary
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Keypairs.Ordinary
```

## Native clock and crypto-helper contracts

The five clock/jitter contracts and seven Noise-helper contracts now preserve
the actual `WGWorld`, with unrestricted Ambient inputs and outputs. These helpers
are genuinely `WG.M`; their preservation follows from their bodies, not subsystem
separation alone. The four snapshot contracts retain key derivation, the getter's
current-slot fact, the setter's existing-cell premise and decryption's snapshot
preservation even when decryption rejects or invalidates a receiving key.

Two Ambient-only compatibility frames are deleted. Three additional deleted
wrappers duplicate retained canonical native contracts; their remaining Session
callers still need redirects and remain lagging. No success, validity or liveness
premise was added, and no failed-state preservation or totality claim is made.

Validation: frozen scoped build passes (84 jobs); all 100 module-owned
declarations, including the 16 explicit theorems, use only permitted axioms;
fresh OrdinaryHot kernel replay passes. Independent frozen-source review confirms
the complete claim and deletion ledger with no substantive findings. Source and
artifact hashes, trust scan, terminal preservation, mirror equality and whitespace
pass. Of five capped calls, one temporary axiom-enumeration checker failed for a
missing import; correcting that checker alone passed. There was no source proof
failure, admission, recovery admission, crash, interruption, timeout, KILLED
outcome, limit increase or infrastructure rerun. All handles are collected.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Keypairs.OrdinaryHot
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Keypairs.OrdinaryHot
```

## Native WG store and keypair composition

The pure `WGStoreView` retains exactly the seven fields observed by its old
explicit view. It factors the lifetime snapshot without reconstructing an
execution world. The conditional `snapshot_modify` contract remains: an arbitrary
WG update must preserve the device and keypair counter. This condition is not
given by the new types. The ordinary-update relation and current-slot replacement
premise also remain. Generic `SameView` composition supplies the pure/bind rules.

All 27 surviving theorems are retyped, including two renamed native contracts.
The four deletions are one obsolete Kernel transport and three Ambient-only
snapshot frames. Four scoped examples exercise the native `frame_same`,
`frame_ordinary`, `ordinary_step` and `snapshot_step` macros. Their unported
callers remain lagging. The composition layer no longer imports `Logged.RxPoll`
incidentally; its tactic elaborators import their actual Lean dependency.

Validation: frozen scoped build passes (88 jobs), all 31 explicit named
declarations print only permitted axioms, and fresh SnapshotRules kernel replay
passes. Independent frozen-source review found no substantive issue. Source and
artifact hashes, census, terminal preservation, mirror equality and whitespace
pass. Of six capped calls, the first build failed because removing the incidental
import exposed a missing direct tactic import; the five subsequent calls passed.
No admission, recovery admission, crash, interruption, timeout, KILLED outcome,
limit increase or infrastructure rerun occurred. All handles are collected.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Keypairs.SnapshotRules
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Keypairs.SnapshotRules
```

## Product scheduler observations

All 26 existing erasure contracts now run over the actual product World and
retain their contract shapes: 17 signatures explicitly qualify `Leanux.M`,
and nine scheduler interfaces retain their written form. Their callback scope
is unchanged. The native validator
observer enters through `liftWGGhost` once, carrying its actual WG and Ambient
outputs and acceptance history. Scheduler records use Ambient; NAPI placement
uses the fixture world. Original `Activation.consistent` trials still execute
on copied actual Worlds, discard their trial state and events, and convert only
hidden-record mismatches to false. The selected committed observer runs once.

The encrypt observer now calls the actual polymorphic `encryptRingPoll`, keeping
ring consumption/write-back before the softirq and then the consumption record.
The decrypt worker retains its distinct softirq-first order. This repairs the
copied-source drift without a device, reachability or success premise. The
checksum callback remains a product action. GRO batching, held packets, budget
checks, reference puts, frees and all original Stops remain in the erasures.

Validation: frozen scoped build passes (49 jobs), all 53 named declarations print
only permitted axioms, and fresh Scheduler kernel replay passes. Independent
frozen-source review found no substantive issue. Hashes, trust scan, terminal
preservation, mirror equality and whitespace pass. Fourteen capped calls completed;
nine development builds failed on lift inference and tactic normalization. Two
failed builds emitted elaboration-recovery admission diagnostics after type errors;
there was no source admission and none in final validation. A successful direct
lift probe omitted explicit `-j1`; the Lake configuration and final axiom check
retained it. No interruption, timeout, KILLED outcome, limit increase or
infrastructure rerun occurred. All handles are collected.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.Logged.Scheduler
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Logged.Scheduler
```

## Native table, removal and packet helpers

Eight claims are carried over their actual monads. The index bucket helpers
retain equality of their own table. Trie removal retains its complete all-input
WG/Ambient execution equation, including each source-positioned component lift
and missing-device guard. Header and padding helpers preserve their complete
native WG state. `checksumHelp` remains a product action, with complete World
equality on normal returns; its rejecting paths remain unconstrained by that
partial-correctness contract.

Three outside-index frames are deleted because the actual index adapter already
establishes structural separation. One unused conditional device-modification
helper is also deleted; its conditional claim is not classified as type-given.
No callback domain, return condition or failure equation was narrowed.

Validation: scoped build passes (38 jobs), all 12 named declarations print only
permitted axioms, and four independent fresh kernel replays pass. Independent
frozen-source review found no substantive issue. Source hashes, trust scan,
terminal preservation, mirror equality and scoped whitespace pass. Eight capped
calls completed: two development builds failed on omitted comparison expansion
and the product checksum failure WP; the frozen build, axiom check and four
replays passed. The failure WP closes by definitional reduction under partial
correctness. No source admission, elaboration-recovery admission, interruption,
timeout, KILLED outcome, limit increase or infrastructure rerun occurred.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.Framing.WGIndex Leanux.Proofs.WG.AllowedIps.RemovalSource Leanux.Proofs.Framing.WGReceiveHeaders Leanux.Proofs.Framing.WGData
# Run separately for each of the four modules above:
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Framing.WGData
```

## Component adapter extension

`Framing.Lift` grows from nine to sixteen theorems; its original nine are
byte-identical and are not counted again. Three exact equations expose the
actual trie, packet-store and routing adapters. The first two keep the device
guard before component execution, their original Stop and their precise field
write-back. Routing receives the current device facts, including absence, and
writes only the returned routing store; returned device facts are discarded.
All three retain the actual Ambient result.

Four Hoare rules transfer these exact executions. The trie transfer retains
return-sensitive and frontier-sensitive component contracts; the three stability
rules apply to arbitrary predicates stable under the relevant component
replacement. They add no execution-success or Ambient restriction and avoid
reintroducing per-leaf structural frames.

Validation: final scoped build passes (11 jobs), all sixteen named declarations
print only permitted axioms, fresh Lift kernel replay passes, and independent
frozen-source review against the actual adapters found no substantive issue.
Hashes, terminal preservation, mirror equality, trust scan and scoped whitespace
pass. Five capped calls completed: the first build failed on record-literal
indentation; two subsequent builds, the axiom check and replay passed. The second
build was followed by removal of unused simp arguments in the new proofs. No
source admission, recovery admission, interruption, limit increase, timeout,
KILLED outcome or infrastructure rerun occurred. All handles are collected.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.Framing.Lift
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Framing.Lift
```

## Native socket/configuration and product evolution

Nine socket/configuration contracts move to actual `WG.M`. Their pure
`WGOwnedView` retains all eleven incoming WG-owned fields: the original seven
store fields plus both IPv4 FIB tables, the timer clock and enqueue counter.
The seven-field view is unchanged. The socket and configuration masks retain
their original device fields and modifier premises. Three read-only helpers
preserve the complete WG state; their proofs follow the actual helpers, not
the monad type alone. Ambient inputs and outputs remain unrestricted, and
ordinary error-valued returns remain distinct from Stops.

All 24 evolution rules retain their product-world/history contract shapes.
Seven statements adapt their source expressions or projection names. Arbitrary
product callbacks, arbitrary World updates with their ordinary-transition
premise, indexed runner boundaries and actual incoming histories remain.
The validator enters through the real `liftWGGhost`; its evolution proof uses
both actual WG/Ambient endpoints and the returned history. One new ordinary
transport theorem uses the actual `liftWG` equation. No compatibility execution
state or narrower callback domain is introduced.

Validation: the closed build passes (93 jobs), all 47 explicit declarations
print only permitted axioms, and three independent fresh kernel replays pass.
Frozen-source independent review found no substantive issue. Source hashes, exact scope, terminal
preservation, mirror equality, trust scan and scoped whitespace pass. Six capped
calls completed: one development build failed on an unspecified base monad in
the generic list rule; the repaired build, axiom check and three replays passed.
One patch-format rejection occurred before mutation. No source admission,
recovery admission, interruption, timeout, KILLED outcome, limit increase or
infrastructure rerun occurred in this port. All handles are collected.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.Framing.WGSocketLifecycle Leanux.Proofs.Framing.WGConfiguration Leanux.Proofs.WG.Keypairs.Evolution.Rules
# Run separately for each of the three modules above:
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Keypairs.Evolution.Rules
```

## Native WGBase and filesystem-wrapper removal

The 185 WGBase contracts become 117 native/generalized contracts: 116 stay in
WGBase and the arbitrary-StateT map rule moves to Framing.Tools. Thirteen
previously ported helper theorems retain their contracts; across the three
edited files the count is 198 to 130. The receive snapshot retains the counter
frontier and every resident internal identity/window. Actual queue, timer,
routing, owner-word and missing-device guards remain, without new validity or
successful-execution premises.

Sixty-six leaf frames disappear: sixteen Ambient, twenty-two trie, twelve index
and sixteen packet-adapter claims. The native component types and generic
adapter rules supply them. Two unused conditional node-view transports also
disappear; these are redundant support, not type-given facts. Borrowed-peer
return-value claims remain for their own carry. Generic map composition still
admits arbitrary product callbacks. Large continuations are proved separately
and applied with their checked contracts; the automation uses definitional
goal replacement and guarded source-head matching.

Twenty-one filesystem-related theorems are removed separately: nine structural
frames, ten redundant generic-lift specializations, and two unused conditional
transport helpers. This deletes FilesystemLocal and FilesystemCalls, four
peer/packet fput/fdput frames, packet-view support and six LifetimeSafety exports.
Actual FS operations, taskWorkRun and dispatch use their native monads and the
exact product lift; they cannot execute WG mutations. The generic lift retains
all returned values, FS/Task/Ambient outcomes, Stops and incoming observer history.
The actual caller compositions still need carrying. In particular, fputFinal's
queued namespace cleanup is distinct from its later product-level execution;
task work retains its pop-before-release order and exhaustion Stop.

Validation: the worker's scoped build passes (92 jobs), all twelve final macro
probes pass, and the root's combined build of the ported closure passes (120
jobs) after removing sixteen named generated artifacts of the deleted modules.
All 130 theorems and both public helper definitions print only standard axioms.
Fresh WGBase kernel replay and the frozen-source independent review pass.
The review also confirms the twenty-one-deletion classification. Source hashes,
retained terminal bodies, mirror equality, trust scan and whitespace pass.

The worker made sixteen capped calls: thirteen builds (twelve failures and the
final pass), two macro probes (one failure and one pass), and one intentional
open-goal diagnostic (failure). One failed build panicked in whnfEasyCases on a
loose bound variable while using continuation generation. Before further edits
or builds, all worktrees were inspected and both dirty trees were preserved,
including untracked files, under
refs/snapshots/proof-campaign-vcgen-panic-20261016T084918Z; branches and normal
indices were untouched. The proof was restructured; it was not retried as an
infrastructure outcome. All sixteen handles are collected. Root build, axiom
check and replay add three passing capped calls. No cap or proof limit was
raised, and no KILLED outcome, guest timeout or infrastructure rerun occurred.
Failed compilation output is not validation. No source admission was introduced.
One root JavaScript syntax rejection occurred before any documentation edit.

The preceding d6f7ed4 checkpoint accidentally used the repository's default
human Git author. This is an attribution error; subsequent campaign commits
use an explicit agent identity per invocation. Existing history is not rewritten.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Keypairs.Frames.WGBase
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Keypairs.Frames.WGBase
```

## Incoming source-observer findings

Product-level former-Kernel observations must retain all 47 original fields:
31 filesystem, three task, two seccomp and eleven WG fields. Native WG typing
does not justify dropping those other observations from an arbitrary product
action. Four old environment frames now encounter FIB writes: `setMtu`,
`routeIntoWg0`, `wgDeladdr` and `wgDelroute`. They require explicit findings,
not removal of the FIB fields from the observation. The route-insertion and route-deletion frames remain
source-inspected candidates.

Capped stdin proofs now establish two unrestricted-state counterexamples and
the corresponding negations of FIB-generation preservation, with only standard
axioms. Using Runner's initial component states, harness Ambient inputs, zero
timing bounds and no hidden records, Env.setMtu 1421 returns zero, changes MTU
1420 to 1421 and changes fib4.rtGenid4 from zero to two. With the WG IPv4 address
present, Env.wgDeladdr4 returns zero, removes it and changes fib4.rtGenid4 and
devAddrGenid from zero to one while fib4C.rtGenid4 stays zero. The old scalar
mask permits only device MTU/inet-flag changes. These are kernel-checked stdin
witnesses; permanent declarations and scoped replay belong to the environment
carry. They are not initialized whole-run security failures.

The preceding checkpoint recorded five MTU probes: one successful evaluation
and four failures, including the default recursion limit; three failed proofs
printed recovery sorryAx and count as failures. This checkpoint adds five
environment probes: one failed direct-reflexivity proof, a passing reduction
diagnostic, two passing fully unfolded witnesses and a passing joint check of
four witness/negation declarations. Full source unfolding closes the proofs
without raised limits. The failed call's recovery axiom print is not validation.

The peer-release observer omits incoming queue and timer guards. Three capped
stdin calls provide exact checked witnesses: a refcount-one queued peer Stops
after the reference write and index removal but before erase; a pending timer
Stops after erase and before retirement; a staged-only packet list permits
release and contributes its length to txDropped. Two calls pass with standard
axioms. The middle call failed because the staged fixture used bytes in place
of Packet and printed a recovery axiom; the corrected fixture passes.
The event formula must append release exactly when the refcount is one and
both TX/RX queues are empty; pending timers must retain that release event.
Erasure must keep both guards and exact failed prefixes without queue/timer
preconditions. These are unrestricted-state witnesses, not initialized R2
failures. All eight new read-only probe handles are collected, with no files,
limit increase, interruption or infrastructure rerun.

The timer observers still use the old raw-expiry scan and removed `fireTimer`.
Actual `runTimers` uses `TimerWheel.nextDue`, dispatch validation, step completion,
detach, `timerPassStep`, callback execution and clearing in order. Expiries 64 and
65 share bucket expiry 72 at level one: with enqueue stamps one and two, wheel
order selects the latter while raw-expiry order selects the former. The source
observers and receipt boundaries must follow the actual inline execution. This
selection witness is likewise source-inspected, pending formal checking.

The success-observer lane had additional copied-source drift. Its old encrypt
worker ran the softirq before consuming the ring; the mirror consumes and
writes back the ring first. With no device and a softirq that throws a hidden
failure, the old copy reaches that failure while the mirror first reaches the
missing-device invariant. This is a source-derived witness recipe, not an
executed counterexample. The decrypt worker still runs its softirq first and
retains that ordering. The scheduler port above repairs this observer and proves
its unrestricted erasure. The remaining runner copy omits
the current routing-table boot, foreign-namespace boot, exact startup failure,
startup-record clearing and per-operation `hiddenAhead`. Its environment copies
omit routing/neighbour calls, route-MTU propagation and the current timer-pass
and advance-window rules. Its syscall copy omits the final `fib_trie` observation
on route-changing operations. These source-inspected observer defects require
current control-flow carry and exact erasure proofs; they are not mirror findings.

## Incoming merge and remaining work

The incoming model build passes (66 jobs), executable build passes (130 jobs),
and the five-module unit suite passes (131 tests, one skip). The first unit run
failed 11 tests because the old executable had not been rebuilt; one
infrastructure rerun after the executable build passed. The initial full proof
build fails at 14 state-split/carry dependencies; no full proof-gate pass is
claimed. The incoming whitespace speedbump reports existing patch whitespace
and a unit-file trailing blank line; those incoming files remain unchanged.

Next are the remaining native/product observers and within-subsystem contracts,
beginning with native component and source-helper contracts.
The broader structural-frame layers
have been deleted with their independently classified unused support; their
surviving consumers still need the actual subsystem adapters.
The incoming branch also includes pre-split send ordering, timer-wheel and
peer-removal changes; their source observers must be carried in actual order.
The runner and callback compositions keep the product world, and failing
prefixes retain history without inventing a failed post-state. No guest or
differential run is part of this proof retrofit. No main integration or push
has occurred.
