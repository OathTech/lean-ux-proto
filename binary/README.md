# Binary adequacy and concrete probe

Work in `.worktrees/binary-tv` on `task/binary-tv`. The standalone package
uses Lean v4.35.0, the mirror by path, and the private Kraken checkout at
`.deps/kraken`. The oracle `.artifacts/kernel-net-choice-s4/vmlinux` is
read-only. No dependency download or global configuration change is needed.

`LookupAdequacy.lookup_simulation` proves entry-to-original-return execution
of `wg_index_hashtable_lookup`, including the complete bucket loop and the
NULL, zero-count and accepted live peer-get paths. Its premises are the
named decoder/service contracts, `SerializedEnvironment` and
`InvocationPermissions` in `TrustBase.lean`, the witnessed
`Pre_lookup`, and acceptance of the executable mirror's run. It proves the
ABI result, live output word, exact source decision/call history, minimal
WireGuard R at actual correspondence points and anchored cuts, and the
endpoint/cut memory footprint. Its returned history exports the serialization
and permission audit, including callback interiors and RET, stopping before
the caller continuation. There is no positive-peer restriction.

`LookupAdequacy.lookup_transport` transports predicates on the same accepted
source run through R. `LookupFrameTransport.lookup_framed_transport` adds
untouched observations using initial physical interpretation, insensitivity
to the proved write footprint, and a source frame theorem. These are frame
premises, not new clauses of Pre or R.

`LookupSourceFrame.lookup_receivingSnapshot` proves that lookup leaves the
allocation frontier, keypair existence, lifetime stamps and receiving
counters/bitmaps unchanged at every logged source point and return.
`LookupSnapshotTransport.lookup_snapshot_transport` instantiates the generic
frame rule with exact frontier and source-live stamp/counter/bitmap bytes.
It does not establish physical allocator membership or absence. Its initial
representation and separation premises are additional to Pre; the existing
Pre witness does not witness them. Whole receive/trace replay-protection
results await their anchored functions and the charter's realism check.

The milestone report, measured rate and verbatim trust surface are in
[the adequacy report](../docs/2026-10-15-binary-adequacy.md#milestone-1-function-theorem-and-review-handoff).
The independent milestone-1 review approved proceeding with named fixes.
Per the user’s resume instruction, milestone 2’s review rechecks those fixes;
there is no separate review before starting it.

## Sequential sibling experiment

On `task/binary-proof-refactor`, `SequentialLookup.lean` adds
`Binary.Sequential.lookup_simulation`. It retains the original `Pre_lookup`
and proves endpoint effects for the full index lookup, including its bucket
loop and NULL/dead/live peer paths. Its separate relation contains current
bucket/owner/count bytes; decisions and cut alignment are not observations.
It reuses substantial physical and bucket proofs from M1.

This is an intentionally unrealistic sequential experiment, with no
concurrent-context claim and no exported execution-wide permission audit.
The original M1 theorem and trust surface are unchanged. The
[experiment report](../docs/2026-10-16-goal-binary-proof-refactoring.md#sibling-sequential-experiment-result)
records the precise differences, retained dependencies and measurements.
Build with `capped -- lake build SequentialLookup`; replay its closure with
`capped -- lake env leanchecker --fresh SequentialLookup`. An external
sibling export can use `capped -- lake env leanexport SequentialLookup`,
redirected to an ephemeral file under `../.tmp`, followed by the existing
`lake check --from-export` form outside Nono. No external acceptance of this
sibling is claimed.

## Executable reconstruction experiment

The sibling worktree `.worktrees/binary-pair-runner`, branch
`task/binary-pair-runner`, implements the first part of the
[paired-execution plan](../docs/2026-10-16-plan-executable-binary-correspondence.md#first-runnable-slice).
It preserves the existing M1 theorem and trust declarations. From that
worktree's root, regenerate and run either recorded workload:

```sh
LEANUX_QEMU_SLOTS=16 capped -- /usr/bin/python3 -B binary/pair_run.py --trace d1_second_response
LEANUX_QEMU_SLOTS=16 capped -- /usr/bin/python3 -B binary/pair_run.py --trace d1_wrong_receiver_index_same_bucket
```

Use a Python interpreter with pyelftools installed (`python3` on ordinary
machines). `--check PATH` reuses a successful differential check containing
raw binary coverage. The existing three-way comparison runs first. The
paired executable then checks reconstruction at entry, successive loop
headers, the loop exit and return, with actual decoded service bodies.
Its JSON inputs, outputs and logs remain ephemeral under `.tmp/binary-pair/`.

These are **constructed entry heaps**, generated from a recorded mirror
prefix, plus labelled synthetic cases. They are not captured kernel memory.
The sequential fixture has no pending softirq and no concurrent interference;
the two undefined-value seeds are tests, not quantification over choices.
Reconstruction covers table membership/order within buckets, embedded owner
words and peer reference counts. It does not reconstruct a whole World.
Environment records and diagnostic histories remain separate.

`capture_lookup.py` separately captures actual entry/return registers and
memory on a rerun of that recorded workload, using QEMU TCG hardware
breakpoints and register/memory reads. After the first command above, use
its successful differential recording directory for `--check`:

```sh
LEANUX_QEMU_SLOTS=16 capped -- scripts/in-bundle python3 -B binary/capture_lookup.py \
  --input .tmp/binary-pair/d1_second_response/input.json \
  --check .artifacts/check/<recording> --out .tmp/captured-lookup \
  --execution-mode sequential
capped -- python3 -B binary/pair_capture.py \
  --capture .tmp/captured-lookup --check .artifacts/check/<recording>
```

Use a fresh output directory; existing snapshots are refused. The snapshot
contains real pointer-reachable objects, stack, per-CPU/task fields and a
bounded part of the KCOV buffer. Uncaptured bytes remain absent. The selected
query/mask and completed-operation prefix identify the invocation. Sequential
mode (the default) verifies QEMU's ENABLE|NOIRQ|NOTIMER stepping mode and steps
to the original return, deferring IRQs and timers inside the call. This is the
intentionally unrealistic sequential environment; `--execution-mode ordinary`
retains ordinary scheduling for diagnosis and is not accepted by this replay.

The replay checks the image/Kraken pins and the existing three-way comparison,
then resolves the source prefix's hidden inputs from this capture's own boot.
`PairCapture` loads its actual bytes and scalar registers without relocation or
zero filling. `PairIndex.lookupFrom` runs the same segment assertions used by
the constructed tests, with captured call/service addresses and the physical
preempt word. The final comparison checks the exact instruction sequence, all
general registers, Kraken's six status flags, every captured return byte and
reconstruction equality with the source. Both index workloads pass under two
undefined-value seeds. This is a concrete test, not a new simulation theorem.
Snapshots and console output are ephemeral. The original `pair_run.py` command
continues to use constructed heaps.

`PairNextProof.next_segment` proves one symbolic back edge using the same
executable reconstruction, reusing M1's physical region lemma. Its explicit
premises are initial reconstruction equality and a successful executable
next-pointer read. It uses `Effects.All`, so it exports no permission audit
and is not a new function-level simulation theorem. Build and replay from
`binary/` with:

```sh
capped -- lake build binary-pair-runner PairNextProof
capped -- lake env leanchecker --fresh PairNextProof
```

The module prints both new theorems' axioms. Local replay does not constitute
the external gate below. An export for that gate can name `PairNextProof`;
the original M1 export does not cover the new executable definitions.

## Build and trust checks

All heavy commands run through `capped`; a KILLED banner or timeout fails.
The charter-authorized binary gate builds the default package, prints the
headline/witness axioms and checks proof sources for escapes. Before building,
it requires agreement between the lock, `TrustBase.krakenCommit`, the resolved
private path dependency and its clean Git HEAD (including untracked sources).
It prints the headline types, invocation-boundary definitions, R/postcondition
and verbatim trust declarations, and diffs `TrustSurface.expected.txt`:

```sh
capped -- scripts/proof-gate --binary
```

An intended surface change updates the specification explicitly, after
inspecting the changed statement/premises, and commits that diff for review:

```sh
capped -- python3 binary/surface.py --write-expected
capped -- python3 -B -m unittest binary.test_trust_gate
```

The gate never updates the expected surface automatically. The baseline is
the reviewable specification, not a retained execution log.

Kernel replay and export preparation, from `binary/` with its v4.35.0
toolchain:

```sh
capped -- lake env leanchecker --fresh LookupSnapshotTransport
capped -- lake env leanchecker --fresh LookupWitness
capped -- lake env leanchecker --fresh LookupHitWitness
capped -- lake env leanexport LookupAdequacy LookupSnapshotTransport LookupWitness LookupHitWitness TrustBase Execution > ../.tmp/binary-m1.ndjson
```

`--fresh` takes one module per invocation. The export is ephemeral (about
1.1 GB for the original M1 closure), not an evidence bundle to commit. Generate
it from the exact commit being claimed, after a successful build, and record
the commit and modules with the result. Export generation must finish with
exit zero; a partial export from a failed job is not a gate input.

The external gate is run by the user **outside Nono**, still from `binary/`:

```sh
capped -- lake check --from-export ../.tmp/binary-m1.ndjson
```

The toolchain’s sandboxed project build cannot see this package’s parent path
dependencies. `--from-export` replays the complete exported declaration
closure without that build. Plain `lake check` is not the recipe for this
layout. If an inside-Nono speedbump is needed, use the same export with
`capped -- lake check --inadvisably-no-sandbox --from-export ../.tmp/binary-m1.ndjson`;
do not report that as the external gate.

On 2026-10-15 the user reported external acceptance at **430ea90**, using
`lake check --from-export ../.tmp/binary-m1.ndjson`, exported from
`LookupAdequacy`, `LookupSnapshotTransport`, `LookupWitness`, `TrustBase`
and `Execution` (before the hit-witness module existed). Its exact output was
“Lean default kernel accepts the solution; uses axioms: propext, Quot.sound,
Classical.choice”. That result does not cover subsequent surface changes;
regenerate the export for the milestone-2 claim point, adding its headline
modules to the command. Remove the export after the check when it is no longer
needed.

The accepted proof axioms are only `propext`, `Classical.choice`, and
`Quot.sound`. Milestone 1 uses bespoke per-path composition. The unused
`compose_regions` helper was retired in review fix F5.

## Concrete tests

From the worktree root, regenerate a recorded operation and compare Kraken,
ordered kernel coverage/comparison operands, and the mirror's decisions:

```sh
LEANUX_QEMU_SLOTS=16 capped -- /usr/bin/python3 -B binary/run.py --trace d1_wrong_receiver_index_same_bucket
LEANUX_QEMU_SLOTS=16 capped -- /usr/bin/python3 -B binary/run.py --trace d1_second_response
```

`--check .artifacts/check/<run>` reuses a completed recording with the raw
per-invocation streams; older recordings without them fail. System Python
needs pyelftools. The probe checks the private Kraken pin, ELF identity,
region decoding and explicit failure outcomes. It tests actual service
bodies separately; service contracts remain explicit proof hypotheses.

The exact state satisfying Pre is proved by `LookupWitness.witness_pre`.
Execute it from entry to return, from `binary/`:

```sh
LEANUX_QEMU_SLOTS=16 capped -- lake env lean LookupWitnessTest.lean
```

The hit states are proved by `LookupHitWitness.dead_pre` and `live_pre`.
After the `d1_second_response` three-way run, execute both exact states:

```sh
cd binary
LEANUX_QEMU_SLOTS=16 capped -- lake env lean LookupHitWitnessTest.lean
```

The live hit's read projection matches the recorded entry. The dead hit is
its zero-count mutation, and checks the owner-word clear as well as the ABI,
result, count and mirror decisions. Both run all decoded callback bodies to
the original return, with two undefined-value seeds.

This is a state materialized from a recorded operation's mirror read
projection, not a captured kernel entry and not a reachability proof.
`binary/generate.py` regenerates ELF instruction terms and DWARF layouts.
Pointer structures and proofs are hand-finished. `attic/` is outside the
proof path. Generated traces, dumps and build outputs are disposable;
`.tmp` and `.artifacts/check` are not evidence bundles to commit.
