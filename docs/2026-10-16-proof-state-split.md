# Proof campaign: state-split retrofit

The branch `proofs/campaign` carries main `b700659`, including split mirror
`6089dc4` previously merged at `6e0a5c8`.
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
| Keypairs `Ordinary` | 17 | 10 | 3 | 4 | 0 | 14 |
| Framing `WGTime`, `WGHandshake`, Keypairs `OrdinaryHot` | 21 | 16 | 5 | 0 | 0 | 16 |
| WG store view and Keypairs composition (four modules) | 31 | 27 | 4 | 0 | 0 | 27 |
| Logged `RxPoll`, `Tools`, `Workers`, `Scheduler` | 26 | 0 | 0 | 26 | 0 | 26 |
| Index table, trie-removal source, receive headers and data helpers | 12 | 8 | 4 | 0 | 0 | 8 |
| Component adapter extension (new contracts only) | 0 | 0 | 0 | 0 | 7 | 7 |
| Native socket/configuration frames and new WG-owned view | 9 | 9 | 0 | 0 | 0 | 9 |
| Product evolution rules and new ordinary lift bridge | 24 | 0 | 0 | 24 | 1 | 25 |
| Native WGBase contracts and generalized map rule | 185 | 117 | 68 | 0 | 0 | 117 |
| Redundant filesystem-family wrappers and exports | 21 | 0 | 21 | 0 | 0 | 0 |
| Native WGTransitions and cookie contracts | 109 | 108 | 1 | 0 | 0 | 108 |
| Native peer and packet primitives | 45 | 35 | 0 | 10 | 0 | 45 |
| Native peer frames and allocation | 28 | 19 | 8 | 1 | 0 | 20 |
| Product environment contracts and adapters | 28 | 23 | 3 | 2 | 10 | 35 |
| Native AllowedIPs leaves and removal wrappers | 19 | 13 | 6 | 0 | 1 | 14 |
| Native peer-access observer | 21 | 21 | 0 | 0 | 0 | 21 |
| Exact recorded clock tests | 3 | 3 | 0 | 0 | 0 | 3 |
| Native peer-creation observer and generic helpers | 42 | 39 | 3 | 0 | 4 | 43 |
| Native dump sources and generic composition | 19 | 18 | 0 | 1 | 1 | 20 |
| Native device lifecycle and generic factors | 14 | 12 | 2 | 0 | 0 | 12 |
| Native receive admission and lifetime tagging | 9 | 7 | 0 | 2 | 0 | 9 |
| Product GRO callback contracts | 8 | 0 | 0 | 8 | 0 | 8 |
| Native operation frames (`WGMore`) | 126 | 125 | 0 | 1 | 0 | 126 |
| Native mixed-access observers and shared transports | 35 | 35 | 0 | 0 | 2 | 37 |
| Native previous queues and product ring contracts | 19 | 6 | 0 | 13 | 0 | 19 |
| Filesystem product bridge and syscall contracts | 2 | 0 | 0 | 2 | 1 | 3 |
| Native peer/device configuration source factors | 2 | 2 | 0 | 0 | 0 | 2 |
| Product batch source and generalized prefix contracts | 5 | 2 | 0 | 3 | 0 | 5 |
| Native AllowedIPs store and arithmetic | 18 | 7 | 2 | 9 | 0 | 16 |
| Native zero-timer keypair-store preservation | 1 | 1 | 0 | 0 | 0 | 1 |
| Native borrowing, access and release invariants | 22 | 19 | 0 | 3 | 1 | 23 |
| Product timer receipts, advance and operation observers | 20 | 0 | 0 | 20 | 1 | 21 |
| Native AllowedIPs lookup and placement | 12 | 12 | 0 | 0 | 0 | 12 |
| Recorded timer source factors | 3 | 0 | 2 | 1 | 1 | 2 |
| Native acquisition and generalized ambient contracts | 15 | 15 | 0 | 0 | 4 | 19 |
| Native index-owner and packet-release observers | 19 | 19 | 0 | 0 | 0 | 19 |
| Native AllowedIPs mutation | 18 | 11 | 0 | 7 | 0 | 18 |
| AllowedIPs source and product RX ring journal | 6 | 1 | 0 | 5 | 0 | 6 |
| Product syscall observer | 3 | 0 | 0 | 3 | 0 | 3 |
| Native cookie frames and generalized view transport | 24 | 19 | 5 | 0 | 0 | 19 |
| Native device/peer configuration frames | 4 | 4 | 0 | 0 | 0 | 4 |
| Native keypair release observer | 18 | 18 | 0 | 0 | 0 | 18 |
| Native trie lists and child insertion | 12 | 5 | 0 | 7 | 0 | 12 |
| Native device lifecycle and transmit frames | 39 | 39 | 0 | 0 | 0 | 39 |
| Product syscall composition | 10 | 0 | 0 | 10 | 0 | 10 |
| Canonical total Aip and product Task adapters | 0 | 0 | 0 | 0 | 2 | 2 |
| Product runner/checkpoint observers and receive evolution | 18 | 0 | 0 | 18 | 4 | 22 |
| Native exact trie replacement and graft composition | 12 | 11 | 0 | 1 | 0 | 12 |
| Native/product lifetime receive and release contracts | 43 | 25 | 0 | 18 | 18 | 61 |
| Native allocation, ingress, trie and product runner/environment carry | 116 | 57 | 2 | 57 | 10 | 124 |
| Native allocation/trie carries and product scheduler/worker/environment callers | 172 | 89 | 2 | 81 | 10 | 180 |
| Native routing, allocation, retirement, R6 terminals and product operation evolution | 102 | 50 | 2 | 50 | 7 | 107 |
| Native allocation, lookup, session and routing lifecycle with canonical Seccomp adapter (corrected) | 55 | 38 | 3 | 14 | 10 | 62 |
| Replay terminals, receive admission, key maintenance, clear walks and native failures | 91 | 40 | 3 | 48 | 11 | 99 |
| Native clear endpoints, material derivation and transmit enqueue (corrected) | 48 | 36 | 1 | 11 | 1 | 48 |
| Native session receipts, projection additions, routing histories and RX queue frames (corrected) | 44 | 38 | 1 | 5 | 11 | 54 |
| Cookie/timer observers, affiliation, origin support, routing completions and enqueue admission | 118 | 82 | 5 | 31 | 19 | 132 |
| Native ring cuts/frames, saved-peer maintenance, routing acquisition and keypair affiliation | 116 | 88 | 9 | 19 | 16 | 123 |
| Product TX source/worker, native configuration tail and canonical WG composition | 25 | 3 | 0 | 22 | 8 | 33 |
| Configured identity, AllowedIPs, handshake construction, RX worker and strict TX borrowing | 93 | 50 | 3 | 40 | 22 | 112 |
| Native counter, lookup/cache, TX staging/admission and RX maintenance | 110 | 61 | 5 | 44 | 29 | 134 |
| Key lifetime, affiliation, trie insertion and receive/socket completion | 56 | 44 | 1 | 11 | 14 | 69 |
| Product encryption, IPv4 calls, timer callbacks and receive borrowing | 68 | 40 | 0 | 28 | 17 | 85 |
| Native/product completion, poll and TX disposition projections | 70 | 38 | 0 | 32 | 12 | 82 |
| TX worker, RX removal/GRO and disposition cuts | 48 | 7 | 2 | 39 | 4 | 50 |

The whole tree currently contains 451 Lean files and 6,403 theorems. The completed
changes total 1,818 retyped theorems, 1,638 deletions, 790 retained contract shapes and 326 added.
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
Two terminal files remain unchanged. LifetimeSafety loses six redundant filesystem
exports. FloodResistance retains all six names: five native WG/Ambient contracts
and the existing product advance contract. ReplayWindow and AntiReplay retain all
22 theorem names and two definitions, with eight native/mixed retypes and fourteen
retained product/pure contracts. KeyLifetime retains all thirteen names, with twelve
native contracts and the existing product timer contract. The terminal surface is now
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

## Native transition and cookie contracts

At the cbb4321 checkpoint, all 103 WGTransitions theorems and six cookie
theorems were carried to native WG.M. The later premise correction below
removes one duplicate conditional helper; 108 of the original 109 remain.
The keypair snapshot and ordinary-transition relation retain their frontier,
resident identities and receiving windows. Seven theorem names track the actual
keypairGetNull source and the native cookie observation. No theorem was added. Concrete source inputs and normal-return scope remain;
Ambient inputs and outputs are unrestricted.

The cookie observation retains all eleven WG-owned fields, masking only the
device secret/birthdate and both rate-limiter tables. The device modifier keeps its original mask-preservation premise. The later
review below corrects the generic WG modifier helper's narrowed premise. The source proofs retain
rotation clock/random records, IPv4/IPv6 selection, allocation refusal and Stops.
Transitions use the generic Ambient, Index and packet adapters; timer reads,
wheel guards, queue conditions, owner reads and error-valued returns stay at the
actual source. sendStagedPackets specializes the generic map rule locally.

Validation: closed two-module build passes (95 jobs), all 112 named declarations
(109 theorems, two definitions and one abbreviation) print only standard axioms,
and both fresh scoped kernel replays pass. Independent frozen-source review
passes. Source hashes, two-file proof scope, unchanged terminal files, mirror
equality, trust scan and whitespace pass. Two worker builds completed: the first
failed on the existing pure rate-limiter table choice and the opaque queued-unit
wrapper; local proof fixes produced the passing build. Root axiom checking and
two replays add three passing capped calls. No source admission, scope expansion,
crash, cap or proof-limit increase, timeout, KILLED outcome or infrastructure
rerun occurred. All handles are collected; no ephemeral files were created.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Keypairs.Frames.WGTransitions Leanux.Proofs.Framing.WGCookie
# Run separately for each of the two modules above:
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Keypairs.Frames.WGTransitions
```

## Native peer and packet primitives

The two primitive modules retain all 45 theorems: 35 native retypes and ten
byte-identical pure contracts. Exact getters retain both WG and Ambient state,
and the execution chains pass each returned Ambient to the following call.
Packet allocation, conditional setters, free and subsequent unreadability keep
the original device-epoch and boundedness premises; arbitrary packet modifiers
remain arbitrary. The eight packet wrappers use the actual guarded skb adapter.
Peer reference release retains the actual index unhash, queue guards, erase,
timer guards and retirement; its normal-return retention claim gains no premise.

Validation: the frozen scoped build passes (23 jobs), all 58 named declarations
print only standard axioms, both fresh kernel replays pass, and independent
statement/source review passes. Hashes, the ordered theorem names, unchanged
proof limits, all-proof trust scan, seven unchanged terminal files, mirror
equality and whitespace checks pass. Four earlier worker builds failed on
conversion/spec selection, including the existing 800000-heartbeat limit; no
limit was raised. The first root axiom invocation omitted two inductive
declarations from its census and failed its count assertion; the corrected
invocation checks all 58. All nine validation/development calls are accounted
for: four pass, five fail. There was no panic, interruption, infrastructure
rerun, source admission or observed worker recovery-admission diagnostic.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Peers.Primitives Leanux.Proofs.WG.Packets.Primitives
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Peers.Primitives
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Packets.Primitives
```

Read-only preparation for the remaining product frames used six capped stdin
calls: two passed and four failed. The five environment-bookkeeping candidates
typecheck with standard axioms over a pure observation of the incoming 47
fields; no execution world or mirror wrapper was added. The first attempt had
opaque lift/spec plumbing and five rejected recovery axiom prints. Three
further batch/stack attempts failed on namespace qualification, two default
heartbeat exhaustions and an unavailable tactic; three further recovery axiom
prints were rejected. The stack proof remains open. These calls created no
files, changed no limits and are not permanent declarations or full-tree
validation; the candidate carry still needs its own scoped build and replay.


## Native peer frames and allocation; premise corrections

The peer frame/allocation tranche carries 21 of 28 theorems: 20 native retypes
and one byte-identical pure mapStore allocation contract. Six Ambient-only
wrappers are deleted because their actions cannot access WG state:
hiddenU64_sameKernel and the hiddenU64/hiddenClock/hiddenJiffies/hiddenClock64/
hiddenAlloc peer specifications. Local initializer callers use the actual
generic Ambient lift. samePeerSnapshot_of_sameKernel is a seventh deletion:
obsolete conditional transport, not an unused or type-derived claim. Its live
CreationAccess callers still need migration. The native WG-store factor and its
projection are renamed; no original entry or modifier condition is discarded.

Independent review found that peerCreate_spec had gained equality of four
incoming fields through WGOwnedView. Its entry premise is corrected to
WGStoreView, the original seven-field observation. Arbitrary Ambient endpoints,
occupied-slot allocation, source Stops, and normal inner Except.error outcomes
retain their original meanings; no vacancy, metadata or record-validity premise
is added. The corrected build passes (26 jobs), all 25 declarations print only
standard axioms, fresh replay passes, and the independent frozen-source review
has no remaining finding. The earlier eleven-field version is superseded.

A separate review found the same scope error in the arbitrary WG modifier
helper modify_cookie_spec. Incrementing timerEnqueues preserves the original
cookie store observation but violates its new eleven-field premise. The helper
is deleted as redundant conditional support: generic hoare_modify already
supports any actual state, observation and predicate. Its sole cookie caller
now applies that generic rule locally. The four concrete cookie frames still
prove their stronger eleven-field conclusions, and the device-only modifier
rule retains its original device premise. This reclassifies one previously
retyped transition/cookie theorem as deleted; it does not invalidate the
historical build record. The corrected cookie build passes (34 jobs), all
eight declarations print only standard axioms, and fresh replay and independent
repair review pass.

[AGENT 2026-10-16] Keep separate pure baseline and incoming product observations
and use the generic modifier rule in place of duplicate conditional support.
This preserves original callback scope while allowing separately identified
stronger concrete conclusions; neither observation is an execution world.

Peer development/validation used eight capped calls: six passes and two ordinary
proof failures (allocation equality plumbing and device extraction). The premise
repair was followed by new build, axiom and replay checks. The cookie correction
adds three passing calls. Hashes, ordered names, unchanged proof limits, all-proof
trust scan, all seven terminal files, mirror equality and whitespace pass.
No crash, cap increase, infrastructure retry, source admission or recovery
admission occurred in these source checks.

Three additional read-only Stack stdin attempts all failed: two exhausted the
default heartbeat limit and one exhausted simplification while eagerly
unfolding the guarded source. Its single recovery axiom print is rejected.
These were exploratory calls, not accepted declarations; no source or limit
changed, and the Stack carry remains open.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Peers.Allocation Leanux.Proofs.Framing.WGCookie
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Peers.Allocation
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Framing.WGCookie
```

## Product environment and import repairs

The six-module environment tranche carries 25 of 28 old theorems and adds ten
adapter facts: 23 contracts are retyped or generalized, two retain their product
interfaces, and three are deleted. The new product observations distinguish the
baseline 43 store fields from the incoming 47-field extension. They are pure
projections of the actual product, with a proved factor from 47 to 43; they are
never substitute execution worlds. Arbitrary worker callbacks, filter callbacks
and device modifiers retain their original quantified scope. All four baseline
environment controls carry, including the original family-only delroute request.

Deleted: the unused duplicate runWorker_sameKernel; fixtureSend_sameKernel and
stackExcluded_sameKernel, which are redundant concrete generic-rule instances.
Both source actions remain product-typed. fixtureSend is exactly a lifted Ambient
skipCut; stackExcluded always Stops, as retained by stackExcluded_failure. Their
live consumers must use the generic actual adapter or exact-failure consequence.
The 7aaacb6 report and commit message incorrectly classified these two deletions
as Ambient-only structural frames; this corrects that justification, not the counts. Stack's nineteen failing guards are
processed sequentially by a local head-only reduction tactic, without expanding
continuation bodies or raising proof limits. ObservationSource.observe_eq is
definitional equality against the current source, including routing access,
sorting, queue clearing and final statistics.

Two previously carried arbitrary-action transport premises in WGBase now use
the baseline seven-field socket/configuration masks. Their four concrete callers
factor stronger eleven-field conclusions down explicitly. A timer-only modifier
must remain admissible; imposing the larger observation was an unjustified
premise restriction. These repairs change no declaration counts.

A combined import exposed duplicate sparse-case definitions generated by Lean
4.35 in separate proof modules. Peers.Primitives now imports Framing.WP, and
WGBase imports Peers.Primitives, so each generated definition has one earlier
owner. The latter edge is acyclic and adds only the primitives module to WGBase's
existing dependency closure. Two getter proofs combine their existing simp/rfl
steps because the earlier realization lets simp close the goal. No statement,
mirror source, toolchain setting or global state changes for this repair.

Validation: the environment worker's final build passes (56 jobs); the combined
root build passes (102 jobs), followed by the repaired WGBase build (93 jobs).
All 182 explicitly named declarations in the eight affected modules print only
standard axioms, including the two private tactic helpers resolved by their
actual environment names. The combined check also imports Logged.WGPrefix.
Fresh replay passes for EnvOperations, Batch, Stack, Peers.Allocation and the
final WGBase. Independent frozen-source reviews, scope/hash checks, source trust
scan and whitespace check pass. The mirror and all terminal statements are
unchanged by this tranche.

The worker used nine capped development calls: two passed and seven failed on
ordinary elaboration obligations. Root used thirteen capped validation calls:
eleven passed and two failed, on the second combined-import collision and an
incorrect private-name spelling in the axiom printer. The five initial fresh
replays passed; WGBase was replayed again after its additional import. There was
no panic, interruption, cap increase, proof-limit increase or infrastructure rerun.

Nine earlier capped stdin probes informed the next carries and these repairs:
three passed and six failed. Three peer-erasure attempts failed (two import
collisions and one default-heartbeat exhaustion); no full erasure proof is
claimed from them. Three AllowedIPs attempts included one passing seven-theorem
check and two failed batches; five recovery axiom prints from the failed batches
are rejected. The WGBase premise prototype passed. Of two primitive import
repair prototypes, the first failed on two already-closed goals and printed four
rejected recovery axiom results; the corrected full-file check passed. These
probes wrote no files. Permanent AllowedIPs and peer-access carries remain next.

Reproduce the scoped compilation and replay with:

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.Framing.EnvOperations Leanux.Proofs.Framing.Batch Leanux.Proofs.Framing.Stack Leanux.Proofs.WG.Keypairs.Frames.WGBase Leanux.Proofs.WG.Peers.Allocation
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Framing.EnvOperations
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Framing.Batch
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Framing.Stack
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Keypairs.Frames.WGBase
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Peers.Allocation
```

## Incoming source-observer findings

The validated `00641c6` baseline has 43 Kernel fields: 31 filesystem, three
task, two seccomp and seven WG fields. The incoming unsplit `e5afc0f` has 47:
`573c9bd` adds the two FIB tables, and `049bd3d` adds the two timer fields.
The preceding report incorrectly described all 47 as original. The two pure
product observations must remain distinct; native WG typing cannot discard
filesystem, task or seccomp observations from arbitrary product callbacks.

The four checked FIB witnesses concern extensions to the incoming 47-field
observation: `setMtu`, `routeIntoWg0`, `wgDeladdr` and `wgDelroute` write those
new fields. Calling them counterexamples to the validated baseline contracts
was incorrect. All four baseline 43-field contracts remain to carry, with
the original device scalar mask for MTU. The enlarged frames fail and retain
their explicit witnesses; their permanent declarations and scoped replay are
pending. Generic callback and modifier hypotheses must preserve their baseline
scope, independently of stronger conclusions proved for concrete helpers.

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

Two additional route witnesses are checked. With the initial component states,
the device running and fixture routes pending, routeIntoWg0 returns normally
and changes fib4.rtGenid4 from zero to three. Deleting its IPv4 default route
returns zero and reduces fib4.infos.size from two to one, while generation
stays three because the alias was not accessed. Actual SameView negations use
those changed projections. Three capped calls comprised one passing evaluation,
one failed full-unfold proof attempt at the default recursion limit, and one
passing four-declaration check using the built-in decide +kernel. The latter
constructs a kernel-checked decision proof, with only standard axioms; it uses
no native proof shortcut or raised limit. All four recovery axiom prints from
the failed call are rejected, not validation.

The timer observers still use the old raw-expiry scan and removed `fireTimer`.
Actual `runTimers` uses `TimerWheel.nextDue`, dispatch validation, step completion,
detach, `timerPassStep`, callback execution and clearing in order. Expiries 64 and
65 share bucket expiry 72 at level one: with enqueue stamps one and two, wheel
order selects the latter while raw-expiry order selects the former. The source
observers and receipt boundaries must follow the actual inline execution.
A capped stdin proof checks both placements, coherent timer/wheel pairs and the
two selector results: five declarations, standard axioms only. The old selector
was copied literally into the probe from the lagging source. This proves a local
selection difference, not an initialized schedule or full-pass failure. The first
probe failed on record-literal indentation and emitted two rejected recovery
axiom prints; the corrected call passed. These five new route/timer probe
handles are collected, with no files, raised limits, crash or infrastructure
rerun. Permanent declarations and replay remain for the corresponding carry.

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

## Native AllowedIPs and generic transport scope

The two AllowedIPs framing modules move from 19 to 14 theorems: 13 native
carries, six deletions and one shared actual liftAip adapter. Read-only leaves
preserve the full AipStore; mutating leaves retain their substantive nextNode
obligation. The removal wrappers preserve the baseline seven-field masked WG
view through each actual guarded lift. Arbitrary Device modifiers retain their
original mask premise. Ambient inputs and outputs, missing-device failures,
child-index guards and finite exhaustion remain unrestricted.

Four deleted helper frames now concern Ambient-only operations. The deleted
allocator frame concerns fields outside its actual AipStore. The sixth deletion,
SameNodeKernel.allocation, is redundant conditional projection support, not an
unused or type-given theorem: its four live consumers in Lifetimes/AllowedIpsInsert
must use the existing generic factor rule and actual adapters when carried.
The allocator consumer there also remains to be migrated. The removal proof
shares compiler-generated continuations through a tactic that constructs checked
proof obligations; no execution world, unchecked proof step or raised limit is
introduced.

A separate scope audit found 26 helpers whose freely quantified product actions
had been narrowed to WG.M, plus an update rule needing generic actual-state
scope. A product action changing only fs.userOut is a concrete excluded original
instance. This checkpoint repairs three transports in WGBase and Peers.Frames:
they quantify actual StateT S m actions and an S-to-WGWorld projection, retaining
the original seven-field premises. Four concrete callers instantiate the
projection with id. The other 23 helpers and snapshot_modify are repaired in the
generic composition checkpoint below. These are repairs to already counted carries, not additional theorems.
Concrete native operations with unchanged modifier predicates do not have that
arbitrary-action restriction.

Validation: AllowedIPs builds in 20 jobs; all 20 explicitly named declarations
print only permitted axioms; fresh replay of WGAllowedIpsInsert passes.
The transport pair builds in 94 jobs, all seven changed transports/callers print
only permitted axioms, and fresh replays of both modules pass. Independent
frozen-source reviews pass. Scope, source trust, unchanged limits, terminal
preservation, mirror equality, census and whitespace checks pass. No full-tree
pass is claimed.

The AllowedIPs worker made ten failed development calls: four default-heartbeat
failures, two unresolved composition-goal failures, two missing tactic/import
failures, one invalid callback-control-flow failure and one doc-comment parser
failure. The callback failure printed an elaboration-recovery admission; it is
rejected, not validation. Root corrected the final comment and the closed build
passed without changing limits. A transport axiom command first failed because
it used the wrong namespace; the corrected command passes. The independently
prepared transport candidate also passed one capped full-source stdin check.

Three separate Clock carry probes remain unvalidated: the first lacked an
explicit import; the next two leave Except error-branch reduction goals, with
rejected recovery axiom prints. No Clock source change is included. All handles
are collected. No crash, interruption, KILLED outcome, guest run, cap increase or
infrastructure rerun occurred in this tranche.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.Framing.WGAllowedIpsInsert Leanux.Proofs.WG.Keypairs.Frames.WGBase Leanux.Proofs.WG.Peers.Frames
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Framing.WGAllowedIpsInsert
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Keypairs.Frames.WGBase
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Peers.Frames
```

## Native peer-access observer and exact clock tests

Peers.Access carries all 21 theorems onto WGPrefix/StatePrefix with every native
WG/Ambient endpoint and incoming history quantified. It corrects copied-source
drift: unhash precedes the queue guard; erase/release precedes the timer guard;
retirement follows both. A queue failure retains read/write only, while a timer
failure also retains release. Missing-object and refcount-zero histories remain
exact. No success, queue-empty, timer-clear or boundedness premise was added.
The concrete finite caller family is unchanged.

KeyTimes.Clock carries all three theorems, retaining signed 64-bit conversion,
multiplication, addition, comparison and returned operands. Both iff statements
name the complete native outputs; comparison recording uses exactly the outgoing
clock Ambient, including its netRx ordinal. Arbitrary seconds, birthdays,
decisions and Boolean transforms remain unrestricted. Downstream Receive and
KeyLifetime terminal callers are still lagging.

The scoped builds pass (Access 55 jobs; Clock 39). All 35 Access and four Clock
named declarations use only permitted axioms. Fresh replays of both modules and
independent full-source reviews pass; source, options, mirror, census, terminal
preservation and whitespace checks pass. Counts are 24 retyped, zero deleted or
added. This remains a partial retrofit, not a full-tree or R5 pass.

Access development used four failed builds followed by the passing fifth:
native reduction/syntax, simp-step exhaustion, queue-history and map comparison
goals, then one reversed key inequality. Its earlier three failed stdin
preparations remain rejected. Clock's fourth stdin preparation passes after the
three failed probes recorded above. Recovery output from every failed call is
not validation. No crash, interruption, cap/limit increase or infrastructure
rerun occurred.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Peers.Access Leanux.Proofs.WG.KeyTimes.Clock
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Peers.Access
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.KeyTimes.Clock
```

## Generic composition scope repair

The six already-carried helper files change from 172 to 169 theorems:
21 contracts regain arbitrary actual StateT actions and their pure observation
functions, 148 retain their contract shape, and three exact duplicate WP wrappers
are deleted. This completes the audit of 26 narrowed helpers plus snapshot_modify,
including the three transports repaired in the preceding checkpoint. These are
repairs of already-counted carries, not new baseline retypes.

SameSnapshot.wp and SamePeerSnapshot.wp are instances of SameView.wp;
OrdinaryAction.wp is the corresponding ProjectedAction.wp instance.
Their native callers now use those generic rules. The substantive
SameSnapshot.ordinary rule becomes SameView.ordinary. Bind, loops, map, discard,
WP characterizations and arbitrary outer modifiers retain product-action scope;
snapshot_modify retains its original two observed-field premises. Concrete
WG.andM/orM and native join automation still describe their actual native actions.
A real product action changing fs.userOut remains a valid generic instance.

The dependent build passes (121 jobs), all 169 theorem axiom reports contain
only permitted axioms, fresh replays of WGBase and Peers.Frames pass, and
independent source review passes. The source/options, mirror, terminal, census
and whitespace audits pass. Whole-tree status remains lagging.

Preparation had three failed stdin calls followed by a passing fourth with
24 affected theorem checks and four product/native instantiation checks.
Failures concerned a missing namespace, generic receiver names and native
instantiations; truncated diagnostics from the second call are not claimed clean.
The final build passed on its first call. The first axiom driver then failed
in its Python parser; both dirty worktrees were snapshotted before correcting
the driver. The corrected check passed without source changes. No limit increase,
KILLED result, timeout or infrastructure rerun occurred.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Keypairs.Frames.WGTransitions Leanux.Proofs.Framing.WGCookie Leanux.Proofs.WG.Peers.Allocation Leanux.Proofs.WG.Peers.Access Leanux.Proofs.Framing.EnvOperations Leanux.Proofs.Framing.Batch Leanux.Proofs.Framing.Stack Leanux.Proofs.WG.Environment.ObservationSource Leanux.Proofs.WG.Keypairs.Evolution.Rules
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Keypairs.Frames.WGBase
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Peers.Frames
```

## Peer creation, dump sources and device lifecycle

These five modules move from 75 to 75 theorems: 69 retyped/generalized,
five deleted, one retained product-interface contract and five added.
CreationAccess is 42 to 43 (39 carried, three deleted, four native bridges);
the dump trio is 19 to 20 (18 retyped, one retained, one added);
device lifecycle is 14 to 12 (12 retyped, two deleted).
All result surfaces remain lagging while downstream callers are carried.

CreationStoreInv replaces the four old invariant laws over a pure store.
Five generic PrefixT helpers retain arbitrary actual StateT S (Except Stop)
actions and observations, including product get and callbacks. Four separate
creation_state_* bridges serve the concrete WGPrefix observer. The missing-device
core still increments peerCounter without events; whole creation instead stops
at its initial getter. An occupied destination may still be overwritten, emitting
allocation/write without an invented release. Cache gating reads Ambient before
WG, and a subsequent clock Stop retains those events without a failed post-state.
CreationCall retains all three complete callers and their ordinary-error/Stop
distinction. No vacancy, queue, timer or clock-success premise was added.

CreationAccess deletes creation_kernel (obsolete conditional monolithic support,
with local callers migrated), creation_branch (a redundant concrete adapter
instance, also with migrated callers), and unused creation_stop. None is justified
by a failed compile. The lifecycle deletions are sameLinkView_of_link (the old
projection transport, supplied by generic factoring) and modifyDev_link_spec
(covered by the canonical modifier rule at fixed spectator state plus the actual
lift adapter). Their local consumers are migrated.

Dump source equalities retain every cursor, guard, failure and the get-before-put
order. Generic composition uses actual StateT actions; its private product
Stop-bind rule is retained, with a separate native counterpart. Lifecycle views
retain seven WG observations. Generic ratelimiter_link carries arbitrary extra
observations on both sides; its product instance can use exactly the old masked
FS/task/seccomp remainder. It does not require equality of extra FS or seccomp
fields. Newlink/create keep their original normal-endpoint alternatives and
unrestricted records. mayHaveSlept and retireDeviceUnits change native bookkeeping,
so their substantive seven-field contracts remain.

Validation passes: CreationAccess build (57 jobs), dump/lifecycle build (40 jobs),
all 62 plus 49 named declaration axiom checks, four fresh entry-module replays,
independent source reviews, source/options, mirror, census, terminal and
whitespace audits. No full-tree gate is claimed.

Creation preparation used eleven stdin calls: calls 1, 4, 8, 10 and 11 passed
13, 20, 26, 34 and 43 theorem checks; the six failures concerned record layout,
folded postconditions, a removed tactic, reducible-only leaf matching, premature
introduction before conditional splitting, and one extra tactic after closure.
Recovery output from failed calls is rejected. The permanent module built on
its first call. Dump preparation had four failures (socket/loop obligations,
tail expansion at the existing limit and lift reductions), followed by a passing
fifth with 20 theorem checks. Lifecycle preparation failed once on trailing
tactics after closed goals, then passed all 12 theorem checks. The combined
permanent build passed on its first call. Its first axiom-check program failed
on a reserved local identifier before checking declarations; the corrected
stdin program passed all 49 checks.
One root replay command failed because --fresh accepts only one module;
dirty worktrees were snapshotted before three separate successful invocations.
No limits or caps were raised; no KILLED result, guest timeout or infrastructure
rerun occurred.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Peers.CreationAccess Leanux.Proofs.Framing.WGDump Leanux.Proofs.WG.NetlinkDump.Source Leanux.Proofs.WG.NetlinkDump.DeviceSource Leanux.Proofs.Framing.WGDeviceLifecycle
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Peers.CreationAccess
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Framing.WGDump
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.NetlinkDump.DeviceSource
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Framing.WGDeviceLifecycle
```

## Receive admission, lifetime tags and product GRO

Receive retains all five claims over actual WG/Ambient execution. It preserves
the exact saved-record prefix, the clock witness and the wire-nonce bound without
adding a bitmap-shape premise. Tagged retains four claims: two native/generalized
and two pure. Its generic focus still accepts arbitrary actual StateT actions;
the separate native focus definition serves WGPrefix observers.

PrefixGro retains all eight product-callback contracts; only the lifted Stop
elimination changes. The arbitrary-world replay counterexample now uses the
actual split initializers and still checks both original guard outputs.
No theorem is added or deleted in these carries. WGBase gains one acyclic import
edge to share the generated add matcher with WGAllowedIps; no statement changes.

Scoped builds pass (Receive 42 jobs, Tagged/WGTransitions 113, GRO/counterexample
76). All 36 checked declarations use standard axioms. Fresh replays and
independent source reviews pass. The whole-tree build at 5403c59 failed on
21 targets; that failure remains the latest whole-tree outcome.

Receive preparation had four failed elaboration calls before a passing fifth.
Its first axiom-check driver then failed on a malformed regular expression;
dirty worktrees were snapshotted before correction. The root combined import
check failed once on an incorrect WGDump module path, then passed. The first
GRO build failed on insufficient lift reduction, then passed with direct
elimination of the impossible successful Stop. No cap or proof limit changed;
no KILLED result, guest timeout or infrastructure rerun occurred.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.KeyTimes.Receive Leanux.Proofs.WG.Lifetimes.Tagged Leanux.Proofs.WG.Keypairs.Frames.WGTransitions Leanux.Proofs.Logged.PrefixGro Leanux.Proofs.WG.ReplayWindow.Counterexamples
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.KeyTimes.Receive
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Lifetimes.Tagged
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Keypairs.Frames.WGTransitions
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Logged.PrefixGro
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.ReplayWindow.Counterexamples
```

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

## Native operation frames and remaining shared observers

This checkpoint carries 208 existing theorems to 209: 178 retyped/generalized,
28 retained contract shapes, two deleted structural record frames and three
added shared bridges. WGMore carries all 126 claims, including arbitrary product
IRQ callbacks. MixedAccess/MixedFrames carry all 35 claims and add two native
bridges while retaining generic StateT/PrefixT transports. Review removed a
duplicated index-adapter derivation in favor of the existing canonical rule.

PrevQueue retains exact malformed Stops and its original coherence premise.
RingSource retains arbitrary product actions and all failure-prefix and
conservation claims. The new general filesystem adapter supports the original
seven-field product netnsClose frame without recreating per-operation FS frames.
Peer/device configuration factors retain unconditional source equalities in WG.M.
The zero timer still preserves the complete transport-keypair map.

AllowedIPs recording now transforms Ambient only, so record_k and commonRecords_k
are deleted on type grounds. Four arithmetic execution laws preserve exact
records and every numeric premise. Node access retains both native endpoints;
the bounded bit and branch selectors generalize to every actual admitted monad.
Their live lookup/graft consumers remain follow-on work.

The batch source factor restores the mirror's route checks, route-MTU propagation
and neighbour calls, retaining its unconditional equality. PrefixBatch keeps
arbitrary product worker callbacks and the original 43-field stability condition;
its renamed view transport generalizes to arbitrary actual states and observations.

Validation: ten scoped builds pass, 243 declaration axiom checks use only standard
axioms, twelve fresh entry-module replays pass, and independent source reviews
pass. No whole-tree gate pass is claimed; the latest whole-tree build still
failed on 21 targets.

Development failures are recorded as failures: WGMore had two preparation
failures (generated-name import collision, then elaboration/existing heartbeat
limit); PrevQueue and RingSource each had one ordinary proof failure; Mixed had
six native run/factor/focus normalization failures before its first passing
build, then a reviewed canonical-adapter repair with another passing build and
axiom check; Syscalls had three failed probes (folded local contracts and missing
loop invariants) before the passing fourth; PrefixBatch failed once on a missing
local type binder; ZeroTimer failed twice (existing heartbeat limit, then local
spec matching). Failed elaboration recovery output is rejected. The AllowedIPs
axiom inventory failed once by reading a comment as a declaration, then passed
with the actual names. No limit/cap increase, KILLED result, guest timeout or
infrastructure rerun occurred.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Keypairs.Frames.WGMore Leanux.Proofs.WG.Lifetimes.MixedFrames Leanux.Proofs.WG.Queues.PrevQueue Leanux.Proofs.WG.Queues.RingSource Leanux.Proofs.Framing.Syscalls Leanux.Proofs.WG.Configuration.PeerSource Leanux.Proofs.WG.Configuration.DeviceSource Leanux.Proofs.WG.Environment.BatchSource Leanux.Proofs.Logged.PrefixBatch Leanux.Proofs.WG.AllowedIps.Store Leanux.Proofs.WG.AllowedIps.ArithmeticMirror Leanux.Proofs.WG.KeyTimes.ZeroTimer
# Run separately for each entry module named above:
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Lifetimes.MixedFrames
```

## Timer receipts, native borrowing and lookup contracts

This checkpoint carries 57 existing theorems to 58: 31 retyped/generalized,
24 retained contract shapes, two obsolete source-support equalities deleted
and three shared/native helpers added. Native borrowing retains all seven
WG-store observations and the pointwise peer store, including refcount success
conditions. Keypair access keeps arbitrary projected actions alongside native
observers; release invariants now describe WGWorld. Lookup and placement retain
all representation, width, address, budget and exact native-store conclusions.

The product operation and advance observers follow the recorded timer wheel,
step guards, end-of-wait guard, reset order and current routing/neighbour paths.
Review found that moving peekUnit outside the timer receipt consumed passive
records before its captured boundary. The final timerDispatchUnit keeps that
lookup, all dispatch checks, detachment, callback and reset inside the captured
action. The outer selection is pure. Independent re-review and fresh replay
cover the repaired version; the earlier passing erasure proof did not establish
receipt adequacy. The arbitrary product callback domain remains intact.

TimerSource removes the vanished raw-scan fireTimerSource_eq and firstDue_eq
support and adds the unconditional recorded-wheel source equality. This is a
source-API replacement, not a type-trivial deletion. The separate documented
raw-expiry versus recorded-wheel finding remains. CursorWitness retains its
exact two observations after retyping the isolated callback to the native
WG/Ambient stack. It makes no runner reachability claim: the current runner
rejects the historical pending-dump replacement recipe.

All ten modules compile in scoped builds. Their 93 named declarations and an
ordinary-decide cursor observation theorem use only standard axioms; nine fresh
entry-module replays and independent reviews pass. Advance's final replay also
covers the repaired TimerPass. The complete proof gate remains pending.

Development failures remain failures: PeerBorrow had two local proof failures;
Lookup three; Placement one; Operations one caused by accidental changes to
source-message literals (restored); CursorWitness one parser failure; Advance
one reset-composition/name failure. TimerPass had fourteen failed builds and
two passing builds, the first pass superseded by the receipt review repair.
Its failures were ordinary normalization, tactic matching and existing heartbeat
limits; the final helper factors the derivation without increasing those limits.
Rejected recovery output is not accepted proof. No cap/limit increase, KILLED
result, guest timeout or infrastructure rerun occurred.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.Framing.PeerBorrow Leanux.Proofs.Logged.Advance Leanux.Proofs.Logged.Operations Leanux.Proofs.Logged.TimerPass Leanux.Proofs.WG.AllowedIps.LookupMirror Leanux.Proofs.WG.AllowedIps.PlacementMirror Leanux.Proofs.WG.Environment.TimerSource Leanux.Proofs.WG.LifetimeSafety.CursorWitness Leanux.Proofs.WG.Lifetimes.KeypairAccess Leanux.Proofs.WG.Lifetimes.ReleaseInvariant
# Run separately for each entry module (Advance includes TimerPass):
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Logged.Advance
```

## Native release, cookie replies and syscall composition

This checkpoint carries 89 existing theorems to 88: 69 retyped/generalized,
15 retained contract shapes, five structural leaf frames deleted and four native
adapters added. Acquire and the owner/packet observers retain exact failure
histories, current-residency and release-uniqueness premises, and both native
state endpoints. Ambient's four projected helpers retain arbitrary actual
product actions and invariants over caller-selected observations; their native
counterparts are additional instances, not restrictions of that domain.

AllowedIPs mutation preserves total component contracts and exact outer
allocation refusal or installed-device results. The source loop retains its
early cleanup. Review caught an initially narrowed continuation; the corrected
helper quantifies over every actual monad admitting the WG and Ambient lifts,
including the product runner. RxRingJournal retains its product-world domain.

Cookie replies preserve the complete device except the original secret,
birthdate and transmit-statistic mask, plus both allocation frontiers. The five
hidden/clock/allocation/routing/cut leaf frames are removed because those native
operations cannot inspect WGWorld; their actual callers use the canonical
adapters. The recorded expiry test remains a WG claim. Generic view factors
retain arbitrary actual action stacks. Review rejected an initially stronger
11-field generic cookie premise; the final transport retains the original
seven-field WG-store observation and its exact mask. The final proof retains branch return
values, so impossible cache paths are eliminated by the recorded decision law.

The logged syscall restores the exact subsystem reset order, seccomp lifts,
return-to-user work and final FIB observation. All three product erasure
interfaces remain unrestricted, including the arbitrary socket callback.

The four device/peer configuration contracts now use the native WG stack;
their normal-only behavior and stable-predicate premises are unchanged.

All ten modules compile in scoped builds; 126 named declaration axiom checks,
nine fresh entry-module replays and independent source reviews pass. A broader
concurrent build failed on 11 targets, including earlier versions of three
subsequently repaired modules. This is a failed integration check, not a pass;
the complete proof gate and terminal replay remain pending.

Development failures: Ambient had one local error-case proof failure; Mutation
had eight failed builds before the passing ninth, involving parser/layout,
local adapter matching and simplification; the logged syscall had one parser
failure before passing. Cookie Frames had six failed builds and two passing builds; the first pass
preceded the scope-review correction and was superseded. Failures involved
ordinary factor/conversion failures, branch-result matching and existing
heartbeat limits; an attempted join-point tactic also produced terms rejected
by the kernel for application type mismatch, plus a parser/layout failure
following the review correction. That attempt was removed, and the
accepted proof uses ordinary exact branch contracts. Rejected elaboration
recovery output is never accepted. The initially narrower AllowedIPs helper
passed compilation but failed scope review; its generalized replacement passed
fresh checks and re-review. WGConfig had one failed build because its tactic
recognizer did not accept the actual generic action head, then passed after
the recognizer repair. No cap or proof limit was increased, and no KILLED
result, guest timeout or infrastructure rerun occurred.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.Lifetimes.Ambient Leanux.Proofs.WG.Lifetimes.IndexOwnerAccess Leanux.Proofs.WG.Lifetimes.PacketRelease Leanux.Proofs.WG.AllowedIps.MutationMirror Leanux.Proofs.WG.Configuration.AllowedIpSource Leanux.Proofs.WG.Queues.RxRingJournal Leanux.Proofs.Logged.Syscalls Leanux.Proofs.WG.Cookies.Frames Leanux.Proofs.WG.Keypairs.Frames.WGConfig
# Run separately for each entry module (Ambient includes Acquire):
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Cookies.Frames
```

## Device lifecycle, release calls and native trie composition

This checkpoint carries 79 existing claims without deleting any: 62 are
retyped/generalized and 17 retain their contract shapes. Two canonical adapter
rules are added. The keypair release observer retains both owner resolutions,
the early NULL and zero-count failures, exact histories, residency and
release-uniqueness premises, and all WG/Ambient endpoints. The device lifecycle
and transmit contracts retain their normal-only semantics, arbitrary snapshot
predicates, stable-predicate premises, signed MTU and routing error paths.
The generic link-view transport remains over arbitrary actual StateT actions.

The trie list and child-insertion proofs retain the original bounds,
distinctness, representation and validity premises. Native Aip contracts state
exact successful results and state updates; the outer insertion retains
allocation refusal versus the installed child. The new total Aip adapter
requires an existing device and transfers the actual component execution and
writeback. It does not discard failed or missing-device cases.

All ten syscall contracts retain their product domain, including arbitrary
product callbacks. One canonical Task adapter replaces per-operation task
frames; actual filesystem and Ambient adapters carry the surrounding descriptor
and record operations. Descriptor acquisition, callback, release, cuts and
temporary rtnetlink socket cleanup retain their source order.

Seven scoped modules compile; 114 explicit named-declaration axiom checks,
six fresh entry-module kernel replays and independent source reviews pass.
ListsMirror's private list-fold proof is covered transitively, not counted
as an explicit axiom print. A broader build failed on ten targets, including
older ChildMutation and WGDevice versions subsequently repaired. The complete
tree gate and terminal replay are still pending; all result rows remain lagging.

Development failures: KeypairRelease had three failed builds while aligning
the actual refcount and index lifts. ChildMutation had five failed builds
while composing native root, placement and allocation results, including
one unsupported tactic syntax and an unintroduced continuation. One axiom
inventory used an invalid private name and failed; its output was rejected,
and the corrected inventory passed. WGDevice had four failed builds:
ambiguous monad inference, routing-head matching and one existing-heartbeat
timeout; the final proof matches the exact routing lifts after decomposition.
Product/Syscalls had one failed adapter proof before using the already-proved
exact lift equation. No limit or memory cap changed, and no KILLED outcome,
guest timeout or infrastructure rerun occurred.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.WG.AllowedIps.ListsMirror Leanux.Proofs.WG.AllowedIps.ChildMutation Leanux.Proofs.WG.Lifetimes.KeypairRelease Leanux.Proofs.WG.Keypairs.Frames.WGDevice Leanux.Proofs.WG.Keypairs.Frames.Syscalls
# Run separately for each entry module, including Framing.Lift:
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.WG.Keypairs.Frames.WGDevice
```

## Runner observations, receive composition and trie grafting

This checkpoint carries 73 existing claims: 36 are retyped/generalized and
37 retain their contract shapes. It adds 22 helpers and deletes no theorem.
The checkpoint and acceptance observers retain the literal current runner
body with exactly their original observation sites. They preserve arbitrary
trace, flag and projection inputs, exact JSON, indexed failures and all guards.
The eleven receive-evolution statements retain arbitrary product callbacks.

Native lifetime leaves retain WG and Ambient endpoints and failure histories.
Enqueue and decrypt-worker callbacks remain unrestricted product actions.
Separate product contracts retain arbitrary full-World invariants and the
original 43-field store-stability observation; the native specializations are
additional claims. The short-circuit helper is generalized over actual StateT
stacks, retaining its former arbitrary action domain.

Exact replacement and graft insertion preserve the original structural
premises, placement/finish contracts, allocation refusal, rollback and installed
results. Aip calls use the actual component adapter. No mirror code changes.

The eleven modules compile in scoped builds. All 129 explicit named
declarations, including private helper theorems, have permitted axioms only.
Six fresh entry-module kernel replays pass. Source review and exact observer
body comparison pass; a separate reviewer also checked the eleven
receive-evolution contracts and their arbitrary callback scope. The default
build passes (66 jobs), and unit tests pass (131 tests, one skip). The broader
proof-tree build fails on seven remaining modules; the proof gate and result
status remain pending/lagging.

Development failures: Checkpoints had 17 failed calls before the passing
eighteenth, involving callback decomposition, equality aliases, existing
heartbeat limits and two diagnostic/command invocations. Its callback proof
was factored without changing the observer. Logged Runner had one failed
head-recognizer match before passing. Evolution Observers had two failed
native-lift compositions before passing. ExactMutation had two failed local
adapter/composition builds before passing; rejected elaboration recovery
output was not accepted. GraftMirror had two failed builds before passing.
The lifetime closure had six failed compositions between its passing adapter
and closure builds. Five axiom-inventory invocations failed on diagnostic
syntax/elaboration context before the corrected inventories passed. One
source-comparison script initially included a trailing documentation comment;
correcting its boundary produced the exact comparison above. Orchestration
parse exceptions and interruption were followed by dirty-worktree snapshots
before resuming. No memory cap or proof limit was raised, and no KILLED result,
guest timeout or infrastructure rerun occurred.

[AGENT 2026-10-16] Keep full-product lifetime interfaces alongside native
leaf specializations: the original contracts quantify invariants and
callbacks that may observe the whole runner state.

```sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake build Leanux.Proofs.Logged.Checkpoints Leanux.Proofs.Logged.Runner Leanux.Proofs.WG.Keypairs.Evolution.Observers Leanux.Proofs.WG.AllowedIps.ExactMutation Leanux.Proofs.WG.AllowedIps.GraftMirror Leanux.Proofs.WG.Lifetimes.ReleaseCalls
# Replay each of the six entry modules separately:
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env leanchecker --fresh Leanux.Proofs.Logged.Runner
```

## Allocation, ingress and runner bounds

This checkpoint carries 114 of 116 existing claims: 57 retyped/generalized and
57 retained contract shapes. It adds ten helpers. Native allocation and receive
contracts retain both WG/Ambient endpoints, exact refusal/failure histories,
record operands and structural premises. Generic state helpers and product
callbacks keep their original arbitrary-action domains. The cookie factor uses
the actual load prefix and cookie result. Trie graft and removal preserve exact
placement, allocation refusal, rollback and installed states.

Deleted: noiseView_record, because recording is Ambient-only and cannot access
the WG Noise view; prefill_initial_snapshot, because seccompPrefill takes only
SeccompWorld and TaskWorld. The product runner proofs instead use the actual
initialWG value and routing adapters. All other product environment and runner
contracts retain their predicates, callbacks and success/failure scope.

The eleven changed modules compile. Axiom inventory covers 184 explicit named
declarations, including eighteen unchanged pure trie theorems; only standard
axioms occur. Eleven fresh entry-module kernel replays pass. Source review
passes; independent EnvLeaves review found a missing bounds guard in a local
proof tactic, which was fixed and revalidated. The last whole-tree build failed
on seven targets; Runner was subsequently repaired. The complete proof gate
remains pending, and every register row remains lagging.

Development failures: GraftStore had one stale rewrite; RemovalMirror had three
adapter/normalization failures; ReceiveAttempts had two normalization/parser
failures; Gate had four factor/normalization failures, including an existing-limit
heartbeat timeout. Allocation had one stale rewrite. Runner/Bounds had one
parser/invariant failure. EnvLeaves had six failed compositions, including an
out-of-range tactic exception; the next build passed, and the reviewed guard
change then passed its build, axiom check and fresh replay. Interrupted diagnostic
orchestration and the tactic exception were followed by dirty-worktree snapshots
before further changes. No limit or memory cap was raised, and no KILLED result,
guest timeout or infrastructure rerun occurred.

[AGENT 2026-10-16] Retain product runner/environment contracts and general
state helper domains; specialize only concrete WG operations to their native
stack. This preserves the old callers' full scope.

## State-split main landing

[USER 2026-10-16] Integrate main b700659 on the campaign branch while
retaining its proof tree, nondefault Lake target and proof gate. These return
to main only with a separately authorized campaign landing.

The merge preserves the complete campaign proof tree and its existing gate
practice and reproduction commands. Main's mirror delta from 6089dc4 is
comment-only; executable code is unchanged. The register now names b700659 as
the retrofit target and keeps cb2348e as the last fully validated mirror.
Counts are unchanged: 451 Lean files, 6,249 theorems and 515 terminal declarations.

Post-merge default build passes (66 jobs); unit tests pass (131 tests, one
skip). Exact source comparison confirms the proof tree, root, target and gate
are unchanged by the merge, and mirror sources equal b700659. A whitespace
check rejected an imported extra final blank line in the split design; it was
removed after a recovery snapshot. The first full proof build after the merge failed at six downstream targets.
The proof gate remains pending and all result rows remain lagging.


## Scheduler, environment, allocation and trie checkpoint

The 16 newly carried files contain 172 old theorems: 89 native or generic
retypes, 81 retained product/pure contracts, two deletions and ten helpers added,
giving 180. The separate ExactMutation correction reuses the canonical
total Aip adapter; its two already-counted theorem statements are unchanged.
The deleted fireTimer pair names a function absent from the current mirror.
Its former raw selector has been replaced by the timer-wheel path, whose
logged evolution callers remain under repair. No theorem is removed merely
because compilation failed.

Worker and scheduler contracts retain arbitrary product callbacks. Environment
proofs keep the actual native lifts, routing effects, lifecycle hooks and
pending-dump guard. Allocation transports keep arbitrary projected state helpers
alongside concrete WG/Ambient contracts. Trie insertion/removal retains source
Stops, exact endpoints, structural premises and the actual ambient continuation
from insertion into lookup. The under-load constructors preserve both recorded
clock endpoints and signed decay comparisons.

Validation: all selected modules build; 215 explicit named declarations use
only standard axioms, and 15 fresh kernel-replay entry checks cover the
17 changed modules. Independent reviews checked the scheduler, worker and
environment contracts and the actual source justifying deletion. The reviewed
ExactMutation adapter duplication is fixed. Source audit confirms unchanged
terminal files, proof limits, trust surface and mirror b700659. Default build
passes (66 jobs); unit tests pass (131 tests, one skip). Reproduce with capped
module builds, explicit named axiom printing and
capped scripts/in-bundle lake env leanchecker --fresh on these module entries.

The next whole-tree build failed at nine targets: AllocationInitial,
KeypairRotation, PeerAllocationFrames, RxQueueView, DeviceRetirement,
FloodResistance.Statements, RemovalCases, ExactMutation and
Keypairs.Evolution.Operations. It observed ExactMutation during its repair;
that module subsequently passed its scoped checks. This is a failed frontier
build, not a whole-tree claim. The gate and all register rows remain lagging.

Development failures remain recorded: scheduler work had an unavailable
dependency and two proof/normalization failures; EnvWorkers had five failed
changed-source compositions, including existing-limit heartbeat failures;
Env had two failures before the explicit lifted WP contracts matched.
AllocationFrames/Audit had two failures, retention one, and release/ambient
one binder failure plus two axiom-driver errors before the complete inventory
passed. InsertionDispatch and the ExactMutation adapter correction each had
one failed proof normalization. No limit or memory cap was raised, and there
was no KILLED result, guest timeout or infrastructure rerun.

A checkpoint-driver path-list error stopped before staging. Dirty worktrees
were snapshotted to recovery refs before correcting the driver; working files
and branches were unchanged by that failed command.


## Routing, lifetime leaves and operation evolution

Twelve carried modules contain 102 old theorems: 50 native/generalized retypes,
50 retained contracts, two deletions and seven helpers added, giving 107.
Routing insertion/refusal and complete removal retain structural premises,
exact WG/Ambient endpoints, allocation frontier bounds and recorded sequencing.
Allocation initialization keeps the original seven-field WG store premise;
queue helpers keep arbitrary projected-state scope. Retirement accounts for
all resident objects, and rotation retains arbitrary product invariant contracts
alongside native specializations. All six R6 terminal names remain.

Deleted: AllocationInv.wgKernel duplicates the existing seven-field store
transport; allocation_prefill frames a Seccomp/Task-only action that cannot
access WG state. Its runner initializer obligation remains to be carried.
No deletion follows from a compile failure. The eleven product evolution
contracts retain their original scope; structural composition first avoids
expanding large continuations. The existing 400,000-heartbeat limit is unchanged.

Scoped builds pass. All 152 explicit named axiom checks use only standard
axioms, including unchanged insertion-coherence and routing-invariant helpers.
Fourteen fresh entry-module kernel replays pass. Independent source reviews
pass; an adjacent stale handshake-queue comment was identified for correction.
Default build passes (66 jobs), and unit tests pass (131 tests, one skip).
Source census, trust scan, unchanged limits and mirror equality with b700659
pass. The proof gate remains pending; every register row remains lagging.
The register summary's previous-checkpoint census omission is corrected here.

Development failures: removal-loop composition had four normalization failures
and one rejected axiom-command syntax error; receive-queue unpacking had one
failure; peer-frame/rotation composition had three failures, including existing-limit
heartbeat exhaustion. Operation evolution had eight failed drafts, including
six with existing-limit heartbeat exhaustion, one unsupported tactic backend,
and the final missing throw branches. The ninth build passed; failed dependent
constant diagnostics were never accepted as results. A draft initializer with
an overly strong whole-WG equality premise was caught and replaced by the
original seven-field premise, then rebuilt and replayed. No limits or memory
caps were raised; no KILLED result, guest timeout or infrastructure rerun occurred.

Reproduce with capped builds of the carried modules, explicit named axiom
printing, and capped scripts/in-bundle lake env leanchecker --fresh on each
entry module (plus unchanged InsertionCoherence and RoutingInvariant).


## Native allocation, lookup, session and routing lifecycle

The next carried group has 55 existing theorems: 39 native/generalized retypes,
14 retained product/pure contracts and two deletions. Ten additions include the
canonical product Seccomp adapter and native counterparts for contracts that
continue to support arbitrary product invariants. The group therefore has 63
theorems, excluding unchanged adapter contracts and the comment-only correction
to the logged batch-completion explanation.

Allocation preserves exact successful and failed prefixes and both Ambient
endpoints. Lookup still resolves and updates the actual nullable index owner.
Its bucket proof reuses the canonical index-table frame. Session retains the
recorded rejection choices and guard order; routing initialization and release
keep the original seven-field store premise and exact refusal outcomes.

Deleted: sessionStateRejected_sameKernel observes only Ambient-owned state;
indexRemove_routing observes fields unavailable to the native IndexM action.
Their consumers use the actual component adapters, with source guards intact.
Both deletions follow from source types and projection definitions.

Scoped builds, all 101 explicit named axiom checks and seven fresh entry-module
kernel replays pass. Source reviews pass; all proof limits and mirror b700659
are unchanged. Default build passes (66 jobs); unit tests pass (131 tests,
one skip). The proof gate remains pending, with every register row lagging.

Development failures: allocation/failure normalization had five failed builds;
device creation had three; session had four; lookup had two and one rejected
axiom-inventory command before repair; routing lifecycle had three. Successful
lookup checks were repeated after replacing a duplicate bucket proof with the
canonical frame. Routing lifecycle also repeated checks after whitespace-only
cleanup; future such cleanup uses token identity and whitespace checking.
No cap or proof limit was raised; no KILLED result, guest timeout or
infrastructure rerun occurred.

Reproduce with capped module builds, explicit named axiom printing and
capped scripts/in-bundle lake env leanchecker --fresh on Product, RoutingView,
RoutingLifecycle, DeviceCreation, LookupAccess, PeerAllocationFailure and Session.


## Replay terminals, receive admission and native failure prefixes

The new carried group contains 91 original theorems: 40 native/generalized
retypes, 48 retained contracts, three deletions and eleven native helpers or
counterparts, giving 99. A separate correction deletes Session's previously
retained indexReplaceHandshake_identity_metadata; the earlier table row is
amended from 39 retyped/two deleted to 38 retyped/three deleted. Its allocation
consumer now applies the canonical index adapter directly. That redundant
frame was a retrofit mistake, not a substantive lost property.

All replay-window and R1 terminal names remain. Native validator sequences
thread each actual WG and Ambient endpoint; arbitrary product observer actions,
runner traces, recorded schedules and placeholder settings retain their original
scope. The inclusive boundary witness is unchanged. Syscall composition retains
all ten product contracts and the original NoReceiveCall classification.
Receive admission preserves both arbitrary product-invariant contracts and the
unrestricted product IRQ callback; its concrete native pure-IRQ call has an exact
bridge. Conditional session-clock and device-work failures retain their complete
source-order journals with consecutive actual operation premises.

The other deletions are indexRemove_identity_metadata and the Ambient-only
recordQueued_sameKernel/queueDeviceWork_sameKernel. They follow from the actual
component types; allocation consumers keep the guarded canonical adapters.
AllowedIPs clear walks retain total child-push results, source-positioned Aip
lifts, original store masks and normal/failed outcome domains.

All scoped builds, 149 explicit named axiom checks, eight fresh entry-module
kernel replays and source reviews pass. Default build passes (66 jobs); unit
tests pass (131 tests, one skip). The proof target/gate, proof limits and mirror
b700659 remain unchanged. The complete proof gate is still pending and every
register row remains lagging.

Development failures: syscall composition had five existing-limit heartbeat
failures and two WP adapter failures before passing at the unchanged limit;
replay terminals had two boundary-normalization failures; receive admission had
six failed drafts including one existing-limit timeout; key maintenance had one
erasure-normalization failure; clear walks had two; each newly carried failure
prefix had one. Failed dependent-constant recovery outputs were rejected.
No KILLED result, guest timeout, cap increase or infrastructure rerun occurred.

A new whole-tree build failed at nine later targets: CookieAccess,
SessionFailure, ReceiveEntryFailure, MaterialOrigin, Queues.Enqueue,
MaintenanceTimers, RxHelperFrames, ClearSnapshot and Peers.Affiliation.
Several were being carried concurrently and subsequently passed scoped checks;
this remains a failed whole-tree run. An output-parser exception in the next
AllowedIPs axiom inventory triggered recovery snapshots of every dirty worktree,
including untracked files, before work resumed; branches were untouched.

Reproduce the carried group with capped module builds, named axiom printing,
and capped scripts/in-bundle lake env leanchecker --fresh on Syscalls,
AntiReplay.Statements, RoutingInitial, ClearWalk, ReceiveEntry, KeyMaintenance,
SessionFailure and ReceiveEntryFailure.


## Clear endpoints, material and transmit enqueue

ClearSnapshot and ClearEndpoint retain all 26 claims: eighteen native or
observation carries and eight pure contracts. The saved-root execution factor,
trie/frontier observations and complete seven-field store mask remain explicit.
MaterialOrigin retains its fifteen original names: four native concrete claims,
eight generic state-domain generalizations and three pure contracts; one generic
nested-state bind inversion is added. Its derivation witness connects each actual
WG and Ambient endpoint consecutively. Queues.Enqueue retains all seven claims,
with six native carries and one generalized store-view transport. The original
success, peer refusal and physical ring-full alternatives remain distinct.

All four files passed scoped builds, 74 explicit named axiom checks, four fresh
kernel replays and independent full-source reviews. Clear's first two builds
failed on source-factor, mask and prestate substitutions; its third passed.
Its first axiom driver failed in Python after Lean completed, and the recovered,
corrected check passed; the recovery snapshot is recorded above. Material's
three validation calls passed without failure. Enqueue's first two builds failed
on proof normalization and the missing packet-store adapter; its third passed,
followed by the axiom check and fresh replay. No limits or mirror code changed.
The default build and unit results from the preceding checkpoint apply to the
unchanged default target and evaluator. Full-tree validation remains pending.


## Session receipts, routing histories and receive queues

This checkpoint carries 44 previously unported claims: 39 native or generic
retypes and five pure contracts, plus eleven additions. The existing 24
PrefixState claims are unchanged and are not counted again. Four generic
projection rules use the lower observer's returned outer state in bind.
SessionOrigin adds seven local composition helpers and carries all seventeen
original names; receipt data stores actual WG and Ambient entry/exit witnesses.
The generic front/tail constructors keep arbitrary target monads and callbacks.

RoutingHistory threads the same outgoing Ambient into the next call.
RoutingRetains preserves its arbitrary StateT action interface through the
explicit ProjectedRetainsRoutingCall projection, beside the native alias.
ConfigurationInputs records the actual guarded insertion cut and final Ambient;
its initialization and rejection observations retain the original seven fields.
All nine RxHelperFrames claims retain complete original helpers, queue identity,
retention and successful-endpoint scope.

Scoped builds, 157 explicit named axiom checks and five fresh entry-module
replays passed, with full-source independent reviews. The axiom count includes
21 unchanged pure declarations in FlatHistory and AddressBounds. Default-target
and unit results carry from the preceding checkpoint because their source
closure is unchanged. The complete proof gate remains pending.

Session's first five development builds failed on dependent-match normalization,
contract introduction, a missing Lean import, and the unchanged heartbeat limit;
explicit source-order composition passed on the sixth. RoutingHistory,
RoutingRetains and ConfigurationInputs each had one ordinary proof failure
before their second build passed. RX helper builds failed on stale identifier
rewrites, adapter/view normalization, the concurrent PrefixState failure, and
loop-invariant typing before the fourth build passed.

RoutingHistory's first axiom check and replay failed because a concurrent failed
PrefixState build left its artifact absent. Each was rerun once after that
dependency was repaired, and both passed; these are the recorded infrastructure
reruns. An RX replay command incorrectly supplied a file path instead of a module
name and failed before resolving the module. The corrected module invocation
passed. Dirty-worktree recovery snapshots are under
refs/snapshots/proof-campaign-checkpoint-driver-20261016T184251Z; branches and
working files were preserved. No memory cap or proof limit changed.


## Cookie, timer, affiliation and completion carry

The new tranche has 118 old claims: 82 native/generalized retypes, 31 retained
product/pure contracts and five deletions, with nineteen additions (132 after).
Two previously carried packet frames are also deleted; the preceding table rows
correct their earlier classification. The eight changed files have 134 old and
146 current theorems. Every result row remains lagging over b700659.

CookieAccess retains all three arbitrary product-invariant contracts and the
original seven-field cookie mask (43 fields at product scope). Self-review
rejected an intermediate eleven/47-field mask because it strengthened the
arbitrary-action premise; the accepted version restores the original domain.
MaintenanceTimers retains ten product-invariant contracts and adds their native
counterparts, with all original branch/clock/Stop behavior.

The obsolete timerArmExpiry factor, its frame and armTimer_source are retired:
the current arm places a timer on the wheel, whereas that old proof-side factor
only wrote expiry. This is a source mismatch, not a type-trivial deletion or a
mirror defect. The native observer now includes the same-expiry return, clock and
enqueue records, all wheel checks and insertion; deletion clears both fields.
Its universal erasure proof and both invariant domains pass.

The distinguishing kernel-checked example starts with one peer, no arm records,
and no previous jiffies. Current armTimer at delay one installs wheel slot two,
bucket expiry two, enqueue stamp one; the obsolete expiry-only operation leaves
no wheel entry. Reproduce from this worktree:

~~~sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean -j1 --stdin <<'LEAN'
import Leanux.Runner
open Leanux Leanux.WG
private def witnessPeer : Peer :=
  { remoteStatic := [], presharedKey := [], precomputedStaticStatic := [], internalId := 1 }
private def witnessWorld : WGWorld :=
  { dev := some { ifindex := 4, ifname := "wg0", peers := Std.TreeMap.ofList [(0, witnessPeer)] } }
private def witnessAmbient : Ambient := { env := Runner.harnessEnv, timing := Env.timing }
private def wheelAfter (a : WG.M Unit) : Option (Option (Nat × UInt64 × Nat)) := do
  let ((_, w), _) ← ((a.run witnessWorld).run witnessAmbient).toOption
  let d ← w.dev
  let p ← d.peers[0]?
  pure ((p.wheel .newHandshake).map fun e => (e.slot, e.bucketExpiry, e.enqueued))
theorem currentArmWheel : wheelAfter (armTimer 0 .newHandshake 1) = some (some (2, 2, 1)) := by
  decide +kernel
theorem obsoleteExpiryOnlyWheel : wheelAfter (do
    let p ← getPeer 0
    setPeer 0 (p.setTimer .newHandshake (some 1))) = some none := by
  decide +kernel
#print axioms currentArmWheel
#print axioms obsoleteExpiryOnlyWheel
LEAN
~~~

Affiliation exposes the actual consecutive owner-read, get and owner-write
executions. Material support uses one WGRunWitness with both Ambient endpoints,
without a new liveness, coherence or success premise. All generic observation
transports retain arbitrary product actions. Routing completions retain signed
ordinary results and append nothing for failed whole calls; three existing
product helpers remain generic beside three new native bridges for callers.

The other three new-tranche deletions are Origins.indexReplace_view and
EnqueueAdmission's getRxSkb_decryptRing/setRxSkb_decryptRing. The prior corrections
delete Enqueue.setTxSkb_encryptRing and RxHelperFrames.freeRxSkb_rxQueues.
The actual index and packet component types cannot change their observed fields;
canonical guarded adapters discharge consumers directly. Retaining those four
packet wrappers was our retrofit form error, including the earlier independent
RX review. The unported poll/combined terminal consumers still need direct
adapters; this checkpoint does not claim full-tree validity.

All eight changed modules passed scoped builds, 225 explicit named axiom checks,
eight fresh entry-module kernel replays and independent source reviews. Standard
axioms only; mirror, caps and proof limits unchanged. The unchanged default build
and unit closure retain their preceding 66-job and 131-test/one-skip passes.
The full 509-target build failed at ReceiveMaintenance, SavedPeers,
RoutingCompletions, EnqueueAdmission, Origins.State and Peers.Affiliation.
Several now pass scoped checks; the whole-tree run remains a failure.

Development ledger: CookieAccess had two proof failures before an intermediate
pass; mask review then required the corrected fourth build and new trust checks.
MaintenanceTimers had eight ordinary proof/dependency failures before its ninth
build passed, including existing-limit failures; no limit was raised. Its first
witness probe omitted a required identity field and failed; recovery axiom output
was rejected, and the corrected example passed. Affiliation and routing
completions each had one failed draft; Origins.State had two (factor inference
and private-name unfolding) before passing. Admission had one factor-elaboration
failure, then passed; deletion review required the final combined 136-job build
and fresh trust checks on all three corrected queue files. Superseded passes
were not used to claim the final source. No KILLED, guest timeout or new
infrastructure rerun occurred.

## Ring cuts, saved-peer observers and routing acquisition

This tranche carries 116 old claims: 88 native/generalized retypes, nineteen
retained product/pure contracts and nine deletions, with sixteen additions
(123 after). The thirteen modules pass scoped builds, 166 explicit named axiom
checks, thirteen fresh entry-module kernel replays and independent source
reviews. The unchanged default build and unit closure retain their preceding
66-job and 131-test/one-skip passes. Every result remains lagging.

Seven packet leaf wrappers, the ambient invariant wrapper and
Keypairs.indexReplaceHandshake_view are removed because their component types
cannot alter the observed fields; consumers use the canonical guarded adapters.
The TX/RX journal interfaces keep arbitrary product callbacks and invariants.
Conditional native ring frames retain peer/keypair retirement and nullable
index-owner reads, with no new residency or coherence premise. Loopback and
socket contracts retain their original seven store fields; the latter permit
WG metadata changes outside that observation. Routing's generic transports keep
arbitrary actual StateT actions and projections.

Saved-peer reads retain exact lookup order and source identities.
MaintenanceCalls retains its old expiry-only setup hypothesis for the clock
failure history, but computes the actual wheel-clearing deletion separately;
the obsolete setup endpoint is never asserted to be that actual endpoint.
Three product contracts remain beside their native counterparts.

Independent review rejected the first TX poll observer as a correspondence
failure: current encryptRingPoll consumes and installs the ring, runs the
callback, then reports the consumed-item decision. The old observer ran the
callback first and only then polled. The corrected cut now contains just the
actual consume/installation before the callback. The worker observer and its
old stepSource_eq still need carrying; this cut's successful checks do not
certify them.

A distinguishing example uses an empty one-slot ring and a callback that
enqueues an empty batch. The actual call returns no item and leaves the batch
queued; the old factor returns the batch and leaves the ring empty. This is a
proof-observer mismatch over unrestricted callbacks, not an initialized-kernel
defect. Both endpoints were kernel checked with only standard axioms:

~~~sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean -j1 --stdin <<'LEAN'
import Leanux.WG.Data
open Leanux Leanux.WG
private def start : WGWorld :=
  {dev := some {ifindex := 3, ifname := "wg0", encryptQueue := PtrRing.init 1}}
private def input : Ambient := {env := fun _ _ => true, timing := ⟨0,0⟩}
private def callback : WG.M Unit := modifyDev fun d => {d with encryptQueue := d.encryptQueue.produce []}
private def oldPoll : WG.M (Option (List SkbId)) := do
  let d ← getDev
  match d.encryptQueue.consume with
  | (none, _) => _ ← branch .encWorkerConsumed false; return none
  | (some item, ring) =>
    _ ← branch .encWorkerConsumed true
    modifyDev fun d => {d with encryptQueue := ring}
    return some item
private def oldFactor : WG.M (Option (List SkbId)) := do callback; oldPoll
private def observe (a : WG.M (Option (List SkbId))) :
    Except Stop (Option (List SkbId) × Option (Option (List SkbId)) × List Bool) :=
  ((a.run start).run input).map fun (out : (Option (List SkbId) × WGWorld) × Ambient) =>
    (out.1.1, out.1.2.dev.map (fun (d : Device) => d.encryptQueue.peek),
      out.2.steps.toList.map (fun (s : Step) => s.outcome))
theorem currentOrder :
    observe (encryptRingPoll callback) = .ok (none, some (some []), [false]) := by
  rfl
theorem obsoleteOrder :
    observe oldFactor = .ok (some [], some none, [true]) := by
  rfl
#print axioms currentOrder
#print axioms obsoleteOrder
LEAN
~~~

ReceiveMaintenance also removes the obsolete queuedThisCall write from its
observer and follows the current pending-work test. The current call appends to
sendWorkQueue but does not append to queuedThisCall. Its erasure and both
invariant domains pass. The checked distinguishing example is reproducible as:

~~~sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean -j1 --stdin <<'LEAN'
import Leanux.Runner
open Leanux Leanux.WG
private def queuePeer : Peer :=
  {remoteStatic := [], presharedKey := [], precomputedStaticStatic := [],
   internalId := 1, lastSentHandshake := -6000000000}
private def queueWorld : WGWorld :=
  {dev := some {ifindex := 4, ifname := "wg0",
    peers := Std.TreeMap.ofList [(0, queuePeer)]}}
private def queueAmbient : Ambient :=
  {env := Runner.harnessEnv, timing := Env.timing,
   hidden := some [{site := HiddenSite.birthdateExpired.info.id,
    bytes := List.replicate 8 0}]}
private def obsoleteQueue : WG.M Unit := do
  if ← branch .queuedNotRetry true then
    setPeer 0 {(← getPeer 0) with timerHandshakeAttempts := 0}
  let p ← getPeer 0
  if ← branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT not then return
  if ← branch .queuedDead p.isDead then return
  peerGet 0
  if ← branch .queuedAlreadyQueued p.handshakePending then
    peerPut (some 0)
    return
  setPeer 0 {(← getPeer 0) with handshakePending := true}
  recordQueued .sendWorker 0
  modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [0]}
  modify fun w => {w with queuedThisCall := 0 :: w.queuedThisCall}
private def queueResult (a : WG.M Unit) : Option (List PeerId × List PeerId) := do
  let ((_, w), _) ← ((a.run queueWorld).run queueAmbient).toOption
  let d ← w.dev
  pure (d.sendWorkQueue, w.queuedThisCall)
theorem actualQueueResult :
    queueResult (sendQueuedHandshakeInitiation 0 false) = some ([0], []) := by
  decide +kernel
theorem obsoleteQueueResult :
    queueResult obsoleteQueue = some ([0], [0]) := by
  decide +kernel
#print axioms actualQueueResult
#print axioms obsoleteQueueResult
LEAN
~~~

The latest complete 509-target build failed at ten frontier modules:
TxRingCuts, RxRingCuts, SocketFrames, SavedPeerLookup, PeerTailRouting,
MaintenanceCalls, HandshakeConstruct, AllowedIpsAccess, ConfiguredIdentity and
Keypairs.Affiliation. Several now pass scoped checks; downstream blocked modules
remain unvalidated and the full gate is pending.

Development ledger: ReceiveMaintenance/SavedPeers needed three builds (getter
normalization, then an existing-heartbeat failure, then explicit composition).
RoutingAcquire/Global needed two (device projection); Keypairs.Affiliation
needed three (lifted/refcount WP, then index-head normalization). Each ring-frame
file needed two (WP adapter heads); the cuts needed two for the same reason.
Review rejected that first passing TX cut's source order; the corrected cut
passed its new build, axiom check and replay. Socket and Loopback each passed
their first scoped build. SavedPeerLookup/MaintenanceCalls needed two builds,
with a residual exact clock-run goal on the first. No proof limit or cap changed.

The first TX witness probe failed because a concurrent rebuild had removed its
imported cut artifact. Its one infrastructure rerun failed ordinarily on tuple
type inference; neither produced accepted endpoint evidence. The changed-source
probe above adds the explicit tuple/result types and imports only mirror code;
it passed. The queued-handshake witness passed on its first call. No KILLED or
guest timeout occurred. Mirror sources remain exactly b700659.

## TX worker and configuration-tail composition

The corrected TX worker now has its complete source equality, erasure and
initialized ring-history contracts over arbitrary product checksum, softirq and
rescheduling callbacks. The consume event precedes the callback; the recorded
consumed-item decision follows it. A failed callback retains the already
installed consume event without asserting a failed-state endpoint. This closes
the TX source-factor repair left pending in the preceding checkpoint.

TX entry retains all eight original product contracts and adds two generic
adapter/loop rules. The worker retains all eleven original contracts.
PeerTailRouting carries three native claims and three product/generic contracts,
adding three native counterparts. Its single observer control sequence supports
both actual interpreters; arbitrary product continuations and address-shape
premises remain unchanged. Three new canonical WG lift laws establish pure,
bind and Ambient composition with exact Stops and product spectator fields.
The seventeen existing Lift claims are unchanged and are not counted again.

This tranche therefore has 25 old claims, three retypes, 22 retained contracts,
zero deletions and eight additions. Four modules pass scoped builds, 65 explicit
named axiom checks, four fresh entry-module replays and independent source
reviews. No nonstandard axiom, mirror edit or limit change occurred. The prior
unchanged default/unit passes still apply; the full gate remains pending and
every result remains lagging.

Development ledger: Lift's first build failed on rewrite targets that lacked
explicit run notation; the second passed eleven jobs. TX entry needed three
builds: the first failed on a substituted return variable and adapter heads;
the second on distributing the lift through conditionals; the third passed.
TX worker needed three local builds: adapter normalization, then one remaining
rescheduling-branch head, then an explicit actual product action closed it.
The final combined build passed 145 jobs. PeerTailRouting needed three builds:
lift/predicate elaboration, an ordinary existing-heartbeat failure with
no-progress simp diagnostics, then bounded composition passed 169 jobs.
There was no infrastructure rerun, KILLED or guest timeout.

## Configured identity, AllowedIPs and handshake/RX callers

Six further modules pass their builds, 176 named declaration axiom checks, six
fresh module replays and independent source reviews. Their 93 old theorems become
112: 50 retyped, 40 retained contracts, three deletions and 22 additions.
ConfiguredIdentity retains all 40 claims, including nullable owners, key
frontiers and generic actual-state transports. AllowedIpsAccess retains its ten
arbitrary product contracts and adds native counterparts; its seven other new
helpers express conditional adapters, actual getter preservation and composition.
The strict TX peer-borrow pair carries its positive pre-count and repayment to
the native WG store. Its unused projection import is removed.

RX entry/worker retain the complete original product callback scope and actual
softirq, consumed-item decision and conditional ring-installation order.
One generic native-to-product bridge replaces the obsolete Ambient failure
wrapper. Handshake construction carries its four exact native erasures and
preserves four arbitrary product invariant contracts alongside four new native
counterparts. The two deleted index-insertion frames observed identities and
allocation metadata outside IndexM's write scope; their deletion follows from
that scope, independently of compilation. Lagging callers will use the canonical
index adapter directly.

The peerMakeDead observer in both configured identity and AllowedIPs had omitted
the current getDev/pubkeyRemoveHashed step. Both now follow the literal mirror
sequence. A present peer with no allowed-IP nodes distinguishes the decision
histories below. This is a proof-observer correspondence finding, not a change
to the mirror or an initialized kernel defect. Both endpoints passed kernel
checking with standard axioms:

~~~sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean -j1 --stdin <<'LEAN'
import Leanux.Proofs.WG.Lifetimes.AllowedIpsAccess
import Leanux.Runner
open Leanux Leanux.WG Leanux.Proofs.WG.Lifetimes
private def nodePeer : Peer :=
  {remoteStatic := [], presharedKey := [], precomputedStaticStatic := [], internalId := 1}
private def nodeWorld : WGWorld :=
  {dev := some {ifindex := 4, ifname := "wg0", peers := Std.TreeMap.ofList [(0, nodePeer)],
                peerHashtable := [([], 0)]}}
private def nodeAmbient : Ambient := {env := Runner.harnessEnv, timing := Env.timing}
private def obsoleteMakeDead : WG.M Unit := do
  modifyDev (deadPeerList 0)
  removeByPeer 0
  modifyDev (deadPeerHashtable 0)
  setPeer 0 {(← getPeer 0) with isDead := true}
private def stepResult (a : WG.M Unit) : Option (List (Decision × Bool)) :=
  (((a.run nodeWorld).run nodeAmbient).toOption).map
    (fun out => out.2.steps.toList.map (fun step => (step.decision, step.outcome)))
theorem actualMakeDeadSteps : stepResult (peerMakeDead 0) =
    some [(.removeListEmpty, true), (.pubkeyRemoveHashed, true)] := by
  decide +kernel
theorem obsoleteMakeDeadSteps : stepResult obsoleteMakeDead =
    some [(.removeListEmpty, true)] := by
  decide +kernel
#print axioms actualMakeDeadSteps
#print axioms obsoleteMakeDeadSteps
LEAN
~~~

Development ledger: ConfiguredIdentity needed eleven builds: accessor/source
repairs, getter/WP normalization, one failed shared-Lift dependency, concrete
creation WPs, pure-state/map congruence and explicit getter witnesses; the final
build passed. AllowedIpsAccess had four failed development builds, then a pass
and a changed-source pass after removing six avoidable helper aliases. A
read-only API probe and its endpoint witness passed. RX needed two failed
development builds and a passing third; its first private-name axiom invocation
failed and was rejected, and the corrected invocation passed. A driver parse
failure executed no tools; recovery snapshots preserved every dirty worktree
before continuation. Handshake construction needed seven builds: erasure
normalization and product composition failures, including two mistaken local
proof edits, then explicit residual branch/KDF contracts closed the module.
No recovery metavariable output was accepted. TX borrow passed its first build.
There was no infrastructure rerun, KILLED, guest timeout, cap or proof-limit
increase in this tranche.

The mirror remains exactly b700659. The previous default build and unit results
cover the unchanged executable closure. The full proof gate and downstream
handshake/staging/NAPI chains remain pending; all result rows remain lagging.

## Native counter, lookup/cache, TX staging and RX maintenance

Twelve modules pass their scoped builds, 189 explicit declaration axiom checks,
twelve fresh module replays and independent source review. Their 110 old
theorems become 134: 61 retyped/generalized, 44 retained contracts, five
deletions and 29 additions. The concrete counter-window observer keeps the exact
comparison operands, short circuit, increment and bitmap failure paths. Lookup
and cache observers retain arbitrary product-history invariant contracts beside
their native counterparts; cache acquisition reads the actual Ambient and WG
flags separately and retains the peer read before a failed refresh clock.

The TX family retains arbitrary product invariants and the original arbitrary
keypair continuation. Native metadata/access, staging and admission contracts
thread the actual WG and Ambient endpoints; rejection and malformed allocation
still retain their reached history. KeyTimes' five generic transports now apply
to arbitrary actual StateT state; its two product branch contracts remain, and
seven native helper contracts are added. The conditional native-to-product TX
contract constructor is an addition, not a substitute for the arbitrary product
contract.

Four RX Skb leaf frames are deleted because their cross-store observations are
preserved by the component's write scope. The lookup getNode wrapper is deleted
as a duplicate of the already-proved native getter contract, not because the
getter's own-store behavior follows from types. RX queue primitives retain
arbitrary product continuations. Maintenance carries twelve substantive
successful-return or retention claims, using actual wheel placement and removal.
Two local tactics factor generated continuations into ordinary kernel-checked
composition proofs; no verification limit changes.

ParserShape's 22 contracts remain. Its old proof-side source factor bounded NAPI
placements by eight; the current parser bounds them by recorded NET_RX section
starts. A one-operation trace with one placement and no hidden records was
accepted by the old factor and rejected by the parser. The repaired factor uses
the literal current count, so its source equality closes again. This is a
proof-observer correspondence finding; it changes no mirror behavior. Both
counterexample endpoints were checked by the kernel using standard axioms.
Reproduce the distinction from the old committed factor with:

~~~sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 python3 - <<'PY'
import subprocess,sys
old=subprocess.check_output(['git','show','91a07ea:Leanux/Proofs/WG/Configuration/ParserShape.lean'],text=True)
fragment=old[old.index('private abbrev source_field'):old.index('private theorem traceSource_eq')]
lean='''import Leanux.Proofs.WG.Configuration.PeerTailRouting
open Lean Leanux Leanux.WG Leanux.Runner
namespace ParserPlacementProbe
private def parseOperation := pinned_const _private.Leanux.Runner.«0».Leanux.Runner.parseOperation
'''+fragment+'''
private def specimen : Json := Json.mkObj [
  ("version", toJson (1 : Nat)), ("id", toJson "placement_probe"),
  ("ops", Json.arr #[Json.mkObj [("op", toJson "pipe2"), ("flags", toJson (0 : Nat))]]),
  ("napi_irq_before_put", Json.arr #[Json.bool false])]
theorem actual_rejects : (Runner.parseTrace specimen).isOk = false := by
  decide +kernel
theorem obsolete_accepts : (traceSource specimen).isOk = true := by
  decide +kernel
#print axioms actual_rejects
#print axioms obsolete_accepts
end ParserPlacementProbe
'''
r=subprocess.run(['capped','--','scripts/in-bundle','lake','env','lean','-j1','--stdin'],input=lean,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
print(r.stdout);sys.exit(r.returncode)
PY
~~~

Development outcomes: the four-module TX chain needed fourteen changed-source
builds (six passes, eight ordinary failures in binder, range, conditional and
product composition); its final whitespace correction preserves proof tokens
and passed the dependent build. TxStagingCalls passed its first build. KeyTimes
staging had one binder/trailing-tactic failure followed by a pass. CounterAccess
passed its native build and its product-extension build. AllowedLookup had one
heartbeat failure from broad rule matching, then passed both narrowed matching
and its product extension. SocketCache passed both builds. ParserShape passed
after the old factor's failed source equality was repaired. The two RX modules
needed fourteen builds (two passes, twelve ordinary failures in normalization,
WP composition and conjunction transport). The first maintenance axiom wrapper
incorrectly rejected wrapped output; its corrected multiline parser passed all
twelve declarations. No failed output was accepted as validation. There was no
crash, infrastructure rerun, KILLED, guest timeout or cap/proof-limit increase.

The intervening whole-tree diagnostic build failed at seven frontiers:
TxContracts, TxDispositionCuts, RxMaintenanceFrames, SocketCache,
AllowedIpsInsert, Configuration.ParserShape and HandshakeConsume. This was
not a count of all remaining downstream failures. Several are repaired above;
the full proof gate remains pending. The mirror remains exactly b700659,
and the prior default-build and unit-test results cover its unchanged executable
closure. Every result remains lagging; R3/R4 work follows the retrofit.

## Key lifetime, affiliation, trie insertion and receive/socket completion

Seven modules pass scoped builds, 91 explicit declaration axiom checks, seven
fresh module replays and independent source review. Their 56 old theorems
become 69: 44 retyped/generalized, eleven retained contract shapes, one deletion
and fourteen additions. The selected-source census excludes concurrently
developed modules.

KeyLifetime retains all thirteen terminal names: twelve native WG/Ambient
contracts and the original product timer contract. The clock operands,
stored-counter bounds, allocation failure history and complete keypair-store
preservation on zeroing retain their original scope; these are the prior R5
disposition, not a new universal lifetime claim. AffiliationCuts carries eight
native source claims and one pure claim. Its null-keypair case uses the current
body-identical null getter and adds no ownership premise.

AllowedIPs insertion keeps four arbitrary product-invariant contracts, including
the arbitrary product action in the allocation lift. Native counterparts use
the real WG-to-Aip adapter only where the source does: polymorphic ambient
arithmetic operations do not acquire an extra missing-device guard. Its masked
allocation view still preserves WG metadata. Four native counterparts and three
private conditional/composition helpers account for its seven additions.

ReceiveFailure preserves the exact bitmap failure and reached keypair read.
ReceiveCompletion retains both original arbitrary product-invariant contracts,
all three receive callback premises, and exact source order and failure history.
Its generic disjunction transport applies to arbitrary actual StateT state;
two native counterparts and two generic native disjunction laws are added.
The ECN frame is an actual own-WG-store claim. SocketSend similarly retains
three arbitrary product-invariant contracts and the arbitrary continuation,
beside three native counterparts; routing reads use the actual routing adapter
and retain IPv6 generation and address observations in order.

RxTxFrames carries seven substantive native claims. The removed newTxSkbs leaf
frame duplicated Skb-component write-scope preservation; its sole caller now
uses the canonical adapter and the generic map rule. The justification is the
component scope, not merely the WG.M surface type or a compiler failure.

Development outcomes: KeyLifetime had one namespace failure then passed;
AllowedIPs insertion had ten changed-source builds, two passes and eight ordinary
failures in adapter selection, binder normalization and conditional composition;
ReceiveFailure had one open-variable reduction failure then passed;
ReceiveCompletion had one broad-rule heartbeat failure then passed its native
and product builds. AffiliationCuts had one adapter/getter normalization failure
then passed. RxTxFrames had three predicate/composition failures then passed.
SocketSend had three elaboration/composition failures then passed. No cap or
proof limit changed, and none of these outcomes was an infrastructure retry.

Two obsolete handshake diagnostics were explicitly cancelled at inspected,
worker-owned PIDs while that separate module remained under development.
One wrapper emitted KILLED for its received termination signal; both outcomes
are failures, neither is a memory-cap pass or an infrastructure rerun. Dirty
worktrees were snapshotted before work resumed. Those diagnostics do not validate
a handshake claim in this checkpoint.

The mirror remains exactly b700659. The full-tree diagnostic and complete gate
remain unfinished, so every result is still lagging; new R3/R4 work follows
completion of the retrofit.

## Product encryption, IPv4 calls, timer callbacks and receive borrowing

Six modules pass scoped builds, 123 explicit named axiom checks, six fresh
module replays and independent source reviews. Their 68 old theorems become
85: forty native/source carries, 28 retained product contracts and seventeen
additions, with no deletion. The prior default build and unit results still
cover the unchanged executable closure. The full proof gate remains pending.

EncryptWorker retains all eleven original product contracts and arbitrary
checksum, softirq and rescheduling callbacks. Its observer now performs the
actual consume and unconditional ring installation before the callback, then
the consumed-item decision and saved-item processing. The earlier ring-order
counterexample in this report applies to this obsolete observer too. No
ownership or ring-geometry premise was added. Four changed-source builds were
needed: three ordinary failures in head normalization, product adapter
transparency and invariant inference, then a pass.

SocketSend4 carries nine native/source contracts, retains seven arbitrary
product contracts and adds seven native counterparts. SocketCalls carries
three native claims, retains its product specification and adds the native
specification. The IPv4 factor now reads the actual FIB generation and socket
namespace, performs both route lookups there, and classifies the neighbor
before tunnel transmission. An empty packet on the one-route specimen below
leaves no neighbor in the old committed tail but adds the current neighbor
entry in the source. This is proof-observer drift, not a Linux finding.
SocketSend4 had one no-progress-simp failure then passed; SocketCalls passed
first time. The first witness probe's ordinary reduction failed and its
recovery axioms were rejected; the second used kernel reduction and passed.

~~~sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean -j1 --stdin <<'LEAN'
import Leanux.Proofs.WG.Lifetimes.SocketSend4
open Leanux Leanux.WG Leanux.Proofs.WG.Lifetimes
namespace SocketFactorWitness
def w : WGWorld := {dev := some {ifindex := 3, ifname := "wg0", sock4 := some 51820}}
def a : Ambient := {env := fun _ _ => false, timing := {advanceWait := 0, traceBound := 0}}
def ep : Endpoint := {family := AF_INET, addr := LOOPBACK4, port := 51821}
def rt : Route := {dev := 1, src := LOOPBACK4}
def oldFinish (e : Endpoint) (bytes : List UInt8) (ds : Nat)
    (exactRx : Bool) (route : Option Route) : WG.M Int := do
  let some r := route | invariant "send4 without a route"
  (pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx
  return 0
def outcome (x : WG.M Int) : Option (Int × List (Bool × Nat × Nat)) :=
  match (x.run w).run a with
  | .error _ => none
  | .ok ((n, w'), _) => some (n, w'.routing.neighbours)
theorem old_result : outcome (oldFinish ep [] 0 false (some rt)) = some (0, []) := by decide +kernel
theorem current_result : outcome (send4FinishSource ep [] 0 false (some rt)) =
    some (0, [(false,1,3)]) := by decide +kernel
theorem differs : outcome (oldFinish ep [] 0 false (some rt)) ≠
    outcome (send4FinishSource ep [] 0 false (some rt)) := by
  rw [old_result, current_result]
  decide
#print axioms old_result
#print axioms current_result
#print axioms differs
end SocketFactorWitness
LEAN
~~~

RxCompletionFrame retains all five native queue contracts, including the
actual lookup acquisition and surviving-resident behavior of completion.
Two normalization/Hoare failures preceded its passing build. RxBorrow carries
twelve native observations and retains both arbitrary product-action helpers,
beside two native counterparts. ProductBorrowed and productView preserve the
former 43-field observation and every complete peer record pointwise; they
are pure observations, not execution states. Repayment still requires only
the original borrowed-result contract, with no added initial liveness or
ownership premise. One no-progress normalization failure preceded its pass.

TimerCallbacks carries eleven concrete native/source claims and retains all
seven arbitrary product-invariant contracts beside seven native counterparts.
Both independent queue-mutation obligations remain. Its zero-key observer was
missing the source's peekQueuedUnit test: a new queue record can describe
requeueing after dequeue even while the mirror still holds the earlier entry.
The corrected observer keeps the acquisition for that requeue and consumes the
record before appending; the old observer instead repaid it. One changed-source
build exposed the stale guard and adapter normalization failures, then the
native and product builds passed. The first witness probe failed on record
layout syntax and its recovery prints were rejected; the corrected probe
kernel-checks both unrestricted-state outcomes below. No initialized
reachability or kernel-defect claim is made.

~~~sh
LEAN_NUM_THREADS=32 LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle lake env lean -j1 --stdin <<'LEAN'
import Leanux.WG.Timers
open Leanux Leanux.WG
namespace ZeroQueueObserverWitness
def peer : Peer := {remoteStatic := [], presharedKey := [], precomputedStaticStatic := [], internalId := 1}
def initial : WGWorld := {dev := some {ifindex := 3, ifname := "wg0", peers := ({} : Std.TreeMap Nat Peer).insert 0 peer, clearWorkQueue := [0]}}
def ambient : Ambient := {env := fun _ _ => true, timing := ⟨0,0⟩, armRecords := true, unitPeers := [(1, Worker.clearPeerWorker.index, 0)], hidden := some [{site := (HiddenSite.queued .clearPeerWorker).info.id, bytes := [1] ++ List.replicate 15 0}]}
def obsolete : WG.M Unit := do
  if ← branch .zeroKeyAlive !(← getPeer 0).isDead then
    peerGet 0
    if ← branch .zeroKeyAlreadyQueued ((← getDev).clearWorkQueue.contains 0) then
      peerPut (some 0)
    else
      recordQueued .clearPeerWorker 0
      modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [0]}
def observe (a : WG.M Unit) : Option (List PeerId × Option Nat × Nat) :=
  match (a.run initial).run ambient with
  | .error _ => none
  | .ok ((_, w), rest) => w.dev.map fun d =>
      (d.clearWorkQueue, (d.peers[0]?).map Peer.refcount, (rest.hidden.getD []).length)
theorem old_result : observe obsolete = some ([0], some 1, 1) := by decide +kernel
theorem current_result : observe (expiredZeroKeyMaterial 0) = some ([0,0], some 2, 0) := by decide +kernel
#print axioms old_result
#print axioms current_result
end ZeroQueueObserverWitness
LEAN
~~~

The intervening whole-tree diagnostic failed at ten frontiers: ReceiveFailure,
TxDispositionCuts, ReceiveCompletion, RxBorrow, EncryptWorker, TimerCallbacks,
RxTxFrames, AllowedIpsInsert, SocketSend and HandshakeConsume. Several have
since passed scoped checks; this list is not all remaining downstream work.
The obsolete handshake child in that build and five worker diagnostics were
terminated only at inspected owned PIDs. All six were collected as failures;
four direct wrappers emitted KILLED for the termination signal. They were
not memory-cap outcomes, passes or infrastructure retries. Dirty worktrees,
including untracked sources, were snapshotted before work resumed.
No proof limit or memory cap changed. Handshake response erasure is being
factored along its literal source continuation; every result remains lagging.

## Native/product completion, poll and TX disposition projections

Six modules pass scoped builds, 115 explicit named axiom checks, six fresh
module replays and independent source reviews. Their seventy old theorems
become 82: 38 retyped/generalized, 32 retained contract shapes and twelve
additions, with no deletion. The executable closure is unchanged, so its
previous default build and unit results still apply. The full proof gate is
pending and all result rows remain lagging.

TxCompletion carries six native/source contracts and retains five arbitrary
product-invariant contracts, beside five native counterparts and a generic
actual-adapter traversal law. Jitter-failure endpoints still follow the
pending-timer read and recorded clock, including both Ambient endpoints.
The source's socket, timer, acquisition and cleanup order remains exact.

ReceivePoll carries three native contracts, retains three arbitrary product
contracts and adds the native two-getter-drop contract. The poll's callbacks
and complete World invariant remain arbitrary. Queue peeking has a concrete
WG.M type; its own-store preservation is therefore a substantive retained
proof, not a foreign-subsystem frame supplied by the split. Erasure covers
the original short-circuit reads, GRO callbacks, release order, failures and
full-budget refusal. Four ordinary elaboration/proof failures preceded the
passing build; guarded composition replaces expensive unrestricted matching.

RxPollPrimitives generalizes the arbitrary-state resident-retention rule,
carries the six other native queue statements, and adds the nested-state
retention rule. Both getters at the original drop remain. RxPollPrefix
retains all four original product theorems, including complete World/Stop
erasure for arbitrary stack callbacks and the failure-retaining removal log.
The pair used four changed-source builds: two passed and two failed in
source-factor or erasure automation. No premise was added.

TxDisposition generalizes six history/algebra rules, retypes its native
source equality, and retains nine concrete product erasures and the pure
bind/conditional rule. Its two additions carry arbitrary native observers
through the actual adapter and its traversal. TxDispositionProjection
carries eleven native appended-history facts, generalizes four actual-state
rules, and retains ten product projection/history contracts. Its additions
are the native observer projection bridge and a generic nested-state
appended-history traversal rule. Saved-head reads, publication, cleanup and
queue-removal order remain the source's.

The eight changed-source build calls for TxCompletion and these two TX
modules produced six failures and two passes. The seventh call built
TxDisposition but failed in Projection; that call is a failure. All final
target builds and separate trust checks passed. These were ordinary proof
repairs, with no infrastructure rerun or cap/limit change.

A separate obsolete handshake build with malformed declaration layout was
terminated at its inspected owned child PID and collected as a failure
(Lean signal exit 143, enclosing build exit 1). No KILLED banner occurred.
Dirty worktrees, including untracked files, were snapshotted before work
resumed. Its corrected replacement remains separate from this checkpoint.

## TX worker, RX removal/GRO and disposition cuts

Five more modules pass scoped builds, 73 named standard-only axiom checks,
five fresh module replays and independent source reviews. Their 48 old
theorems become fifty: seven native/generalized carries, 39 retained product
or pure contracts, two deletions and four additions. No terminal claim or
mirror file changes. The full proof gate remains pending.

TxWorker carries four concrete native/source claims, retains six product
contracts, and adds three native preservation counterparts. The saved head,
two-getter queue drop and completion-before-free/puts order are unchanged.
The product iteration retains its arbitrary rescheduling callback, reached
only after a successful step reporting an item. Three ordinary failures in
adapter matching and composition preceded the passing build.

RxPollOrder retains twelve product/pure contracts, carries two substantive
native queue frames, and adds one generic native-to-product retention rule.
Its callback condition still ranges over arbitrary actual product actions
and permits resident deletion. The getRxSkb queue frame is deleted because
getRxSkb is exactly the SkbStore adapter and the queue observation excludes
that component; the invariant leaf is deleted because it is Ambient-only.
Both uses now use canonical adapters. This reasoning is based on the actual
types and write-back definitions. One ordinary normalization failure preceded
the passing build.

RxPollGro and RxPollGroOrder retain all four and nine original product
contracts respectively. Actual native calls are lifted at their execution
boundaries; occurrence tags, exact returned bytes and failure histories
remain. GroSafe keeps its original chronological meaning and SelectedGroSafe
continues to describe the different selection order. Both changed-source
builds passed first time. The unchanged GroCallback/GroState dependencies
also built, and their seventeen named declarations had standard-only axioms.

TxDispositionCuts retains eight product factor/history/receipt contracts
and carries its native no-send frame. The exact free receipt uses the
starting packet stamp and retains both read and release events. Canonical
Index/Skb adapters and the existing peer-word reader replace structural
leaf expansions. Two ordinary proof failures preceded the passing build.

A separate diagnostic built the independent closure of 49 maximal targets
(305 proof modules, excluding the three active worker frontiers and their
dependents). It failed at DeviceXmit, RoutingSendFrames, LifetimeSafety
Replay/ReplayOrphan, DeliveryOrder ReplayGro, FloodResistance Replay and
KeyLifetime ReplayDelayed/ReplayPostClear. This was a failure, not a
full-tree pass; the replay programs still needed their product projections
carried. No infrastructure rerun, proof-limit increase or memory-cap change
occurred in this tranche.
