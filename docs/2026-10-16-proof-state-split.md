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

| Completed proof change | Before | Retyped | Deleted | Retained interface | Added | After |
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

The whole tree currently contains 449 Lean files and 6,314 theorems. The completed
changes total 224 retyped theorems, 1,468 deletions, 63 retained interfaces and 67 added.
All terminal files remain unchanged. **Every result remains lagging** until the complete tree
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

## Incoming source-observer findings

Source inspection found two observer carry defects beyond type changes. The old
peer-release observer omits the incoming queue and timer guards. With a resident
peer at refcount one and a queued transmit packet, the actual mirror Stops after
the reference write and before erase; the old all-outcome event formula would
append release. A pending timer instead Stops after erase and before retirement.
The observer must retain both guards and each exact failed prefix, without adding
queue/timer premises to erasure. This is an unrestricted-state witness recipe,
not an executed Lean counterexample or a demonstrated initialized R2 failure.

The timer observers still use the old raw-expiry scan and removed `fireTimer`.
Actual `runTimers` uses `TimerWheel.nextDue`, dispatch validation, step completion,
detach, `timerPassStep`, callback execution and clearing in order. Expiries 64 and
65 share bucket expiry 72 at level one: with enqueue stamps one and two, wheel
order selects the latter while raw-expiry order selects the former. The source
observers and receipt boundaries must follow the actual inline execution. This
selection witness is likewise source-inspected, pending formal checking.

The success-observer lane has additional copied-source drift. Its encrypt worker
still runs the softirq before consuming the ring; the mirror now consumes and
writes back the ring first. With no device and a softirq that throws a hidden
failure, the old copy reaches that failure while the mirror first reaches the
missing-device invariant. This is a source-derived witness recipe, not an
executed counterexample. The decrypt worker still runs its softirq first and
must retain that ordering. The runner omits
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
beginning with the projection/composition layer and scheduler observers.
The broader structural-frame layers
have been deleted with their independently classified unused support; their
surviving consumers still need the actual subsystem adapters.
The incoming branch also includes pre-split send ordering, timer-wheel and
peer-removal changes; their source observers must be carried in actual order.
The runner and callback compositions keep the product world, and failing
prefixes retain history without inventing a failed post-state. No guest or
differential run is part of this proof retrofit. No main integration or push
has occurred.
