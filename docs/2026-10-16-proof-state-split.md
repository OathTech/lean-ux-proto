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

| Completed local port | Before | Retyped | Structural deletions | Unchanged | Added | After |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| CounterWindow `Refinement`, `MirrorCalls`, `Bounds` | 31 | 17 | 6 | 8 | 1 | 26 |
| Framing `Basic`, `WP`, `Allocation`, `Index`, new `Hoare`/`Lift` | 40 | 25 | 14 | 1 | 14 | 40 |

The whole tree currently contains 473 Lean files and 7,710 theorems. The completed
ports total 42 retyped theorems, 20 deletions, nine unchanged and 15 added. All terminal files
remain unchanged. **Every result remains lagging** until the complete tree
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

## Incoming merge and remaining work

The incoming model build passes (66 jobs), executable build passes (130 jobs),
and the five-module unit suite passes (131 tests, one skip). The first unit run
failed 11 tests because the old executable had not been rebuilt; one
infrastructure rerun after the executable build passed. The initial full proof
build fails at 14 state-split/carry dependencies; no full proof-gate pass is
claimed. The incoming whitespace speedbump reports existing patch whitespace
and a unit-file trailing blank line; those incoming files remain unchanged.

Next are local/product observer retyping, generic projection/action contracts
and deletion of the broader structural-frame layers.
The incoming branch also includes pre-split send ordering, timer-wheel and
peer-removal changes; their source observers must be carried in actual order.
The runner and callback compositions keep the product world, and failing
prefixes retain history without inventing a failed post-state. No guest or
differential run is part of this proof retrofit. No main integration or push
has occurred.
