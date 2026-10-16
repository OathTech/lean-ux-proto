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

The whole tree therefore currently contains 7,710 theorems. All terminal files
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

## Incoming merge and remaining work

The incoming model build passes (66 jobs), executable build passes (130 jobs),
and the five-module unit suite passes (131 tests, one skip). The first unit run
failed 11 tests because the old executable had not been rebuilt; one
infrastructure rerun after the executable build passed. The initial full proof
build fails at 14 state-split/carry dependencies; no full proof-gate pass is
claimed. The incoming whitespace speedbump reports existing patch whitespace
and a unit-file trailing blank line; those incoming files remain unchanged.

Next are generic partial/total execution contracts, native subsystem lift
bridges, deletion of structural frames, and local/product observer retyping.
The incoming branch also includes pre-split send ordering, timer-wheel and
peer-removal changes; their source observers must be carried in actual order.
The runner and callback compositions keep the product world, and failing
prefixes retain history without inventing a failed post-state. No guest or
differential run is part of this proof retrofit. No main integration or push
has occurred.
