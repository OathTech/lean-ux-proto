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

The allowed-IPs extension runs the same experiment at trie headers, helper
returns and loop exits for IPv4 and IPv6. Prepare its independent three-way
check and run both paired suites from the worktree root:

```sh
LEANUX_QEMU_SLOTS=16 capped -- python3 -B binary/allowedips_probe.py --budget 100000
(cd binary && capped -- lake build binary-pair-allowedips)
capped -- binary/.lake/build/bin/binary-pair-allowedips .tmp/binary-allowedips/input-5.json
capped -- binary/.lake/build/bin/binary-pair-allowedips .tmp/binary-allowedips/input-8.json
```

`allowedips_probe.py --check PATH --budget 100000` reuses an existing
allowed-IPs-profile recording. These trie entries are materialized source
prefixes, not captured kernel states. The suites include persistent repeated
calls, structural variations and corruption controls. A dying peer is an
explicit source refusal, checked against the executed binary retry edge;
it is not a passing lookup simulation. See the plan's tested-trie checkpoint
for counts and the distinction between testing and the remaining symbolic obligations.

The paired sibling's `Binary.Pair.Trie.findNode_checked` in
`PairBoundaryProof.lean` now derives the physical Setup and initial invariant
from the runner's executable `initialBoundary` assertion. It uses one pointer
interpretation computed from Names and retains the named decoder/callback
contracts. `PairBoundaryWitness.lean` supplies kernel-checked positive
IPv4/IPv6 headers and their conditional execution corollaries. This remains
a nonempty-loop-boundary-to-selected-node-exit theorem, before peer-get and
BH-enable; it is not function-entry-to-return adequacy. The added initial
callback-readiness assertion has two rejection controls.

From `binary/`, build and replay the proof, then prepare its external export:

```sh
capped lake build PairBoundaryWitness
capped lake env leanchecker --fresh PairBoundaryWitness
capped lake env leanexport PairBoundaryProof PairBoundaryWitness > ../.tmp/binary-pair-boundary.ndjson
```

Run the external gate outside Nono:

```sh
lake check --from-export ../.tmp/binary-pair-boundary.ndjson
```

On 2026-10-17 the user ran this gate with `capped` for the export of
`PairBoundaryProof` and `PairBoundaryWitness` at `a33869e`. The default
kernel accepted it using only `propext`, `Quot.sound`, and `Classical.choice`.

The [boundary experiment report](../docs/2026-10-16-plan-executable-binary-correspondence.md#executable-boundary-to-physical-loop-2026-10-17)
names the semantic contracts, additional assertions, concrete witnesses,
validation and the limits on interpreting the measured adaptation time.

Allowed-IPs capture uses the same reconstruction, loop assertions and paired
runner as the constructed-state suite. Given the successful recording used by
`allowedips_probe.py`, run from the worktree root (select a Python interpreter
with pyelftools before entering the bundle):

```sh
capture_python=$(command -v python3)
LEANUX_QEMU_SLOTS=16 capped scripts/in-bundle "$capture_python" -B binary/capture_allowedips.py \
  --input .tmp/binary-allowedips/input-5.json --check CHECK_DIRECTORY --out .tmp/captured-trie4
capped "$capture_python" -B binary/pair_allowedips_capture.py \
  --capture .tmp/captured-trie4 --check CHECK_DIRECTORY
```

Use `input-8.json` and a fresh output directory for IPv6. Capture reads both
device roots, their reachable nodes, the device's peer list, entry registers,
stack, query and callback state. Public keys and paths from the two roots
bootstrap the identity map, which stays fixed throughout the call. Headers
and return are captured independently; the replay compares their registers
and bytes, and the complete instruction sequence. Source inputs come from
the completed prefix in that same captured boot. The independent three-way
baseline runs before replay.

At the loop header only, AF is projected out of the extra register comparison:
the preceding XOR/TEST gives it an undefined value in Kraken. Other flags
remain checked; return comparison checks all six. The reconstruction and
boundary assertion were already independent of flags.

This remains sequential QEMU stepping with interrupts and timers deferred.
The current callback assertion requires the entire 32 MiB KCOV allocation;
those bytes are read into an ephemeral `coverage.bin`, not fabricated or
zero-filled. Retaining a full memory at every instruction exhausted the
32 GiB job cap, so the trie runner retains full diagnostic states only at
loop headers while retaining every instruction/access record. The symbolic
execution history is unchanged. The snapshot JSON and sidecar must stay
together and are reconstructible temporary outputs.

Both families pass with two undefined-value seeds: IPv4 has 1,592
instructions and five captured headers; IPv6 has 1,510 and three.
All five capture corruption controls reject. Packet transport tests run with
`capped python3 -B -m unittest discover -s binary -p test_capture_remote.py`. Two-seed replay currently
takes about 3.6–3.8 minutes per family, with roughly 6–7 GiB peak memory.
The [capture report](../docs/2026-10-16-plan-executable-binary-correspondence.md#captured-allowed-ips-extension-2026-10-17)
records the failed attempts, observation correction and measured costs.

The loop theorem now permits the actual entry stack rather than a fixture
address. Its semantic contracts and conclusion are unchanged. The previous
external acceptance above applies to `a33869e`; export the updated closure
with the same modules to `../.tmp/binary-pair-capture-boundary.ndjson` for
the new external gate. Fresh local kernel replay passes; external acceptance
of this generalization is pending. Full function-entry-to-return adequacy
remains open.

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

## Complete-call increment

The [increment plan and report](../docs/2026-10-18-plan-paired-call-increment.md)
tracks executable call-entry readiness, its proof bridge, complete-call
composition and cost measurements. `callBoundary_pre` in `PairCallEntry.lean` derives
physical entry premises from the runner's `callBoundary`; `search_segment`
composes the root and trie search. The complete call theorem is described below.
`PairCallWitness` supplies kernel-checked entry states. Run those exact
states to return using decoded instructions from a prepared allowed-IPs input:

```sh
capped lake build PairCallWitness binary-pair-call-witness
capped .lake/build/bin/binary-pair-call-witness ../.tmp/binary-allowedips/input-5.json
capped lake env leanchecker --fresh PairCallWitness
```

The witness's small buffer intentionally exercises saturation. Paired PC
coverage records count actual stores according to the executable callback
plan; the service body still executes under Kraken. The earlier diagnostic
callback tally was wrong for a full buffer. Other probes retain their prior
callback-tally behavior unless they supply the explicit observer.


The complete-call sibling is now `Binary.Pair.Trie.lookup_checked` in
`PairCallAdequacy.lean`. Successful executable `callBoundary` plus accepted
actual `WG.lookup` execution imply sequential binary return, the matching peer,
exact trie/count reconstruction, restored ABI and callback state, and the
physical write frame. Decoder and callback contracts remain explicit; this
is neither a concurrency theorem nor a proof of the callback bodies.
`PairCallWitness` gives concrete checked entry states and source acceptance
for both address families; `binary-pair-call-witness` executes those same
states to return. The dying-peer retry remains a checked source refusal.

```sh
# From binary/, using capped on shared development boxes:
capped lake build PairCallWitness binary-pair-call-witness
capped lake env leanchecker --fresh PairCallWitness
capped lake env leanexport PairCallAdequacy PairCallWitness PairRemoveOwnership > ../.tmp/binary-pair-call.ndjson
# External gate, outside Nono:
lake check --from-export ../.tmp/binary-pair-call.ndjson
```

The external gate for this complete-call result is pending. The earlier
external acceptance remains specific to `a33869e`. See the
[increment report](../docs/2026-10-18-plan-paired-call-increment.md) for reuse,
failures and measured costs. Captured replay prints separate input, memory
loading and paired-check timings to stderr.

## Fresh removal calibration and runtime costs

From the worktree root, with `LEANUX_KERNEL_DIR` set to the approved oracle
as above, prepare an independent removal-only recording and run the paired
calibration:

```sh
LEANUX_QEMU_SLOTS=16 capped scripts/in-bundle python3 -B -m evaluator.check \
  --suite wireguard --binary-coverage --binary-profile index-remove \
  --trace c_remove_after_handshake --out .artifacts/check/binary-remove
(cd binary && capped lake build binary-pair-remove PairRemoveOwnership)
capped python3 -B binary/remove_probe.py --check .artifacts/check/binary-remove
(cd binary && capped lake env leanchecker --fresh PairRemoveOwnership)
```

The first case materializes the recorded mirror prefix and executes the
source-selected index-removal calls: keypair, keypair, handshake. It compares
kernel coverage and mirror decisions. Arguments are source-derived, not captured,
and intervening caller operations are not executed. Additional generated heaps
exercise collision chains and repeated removals. A stale predecessor pointer
provides a concrete counterexample to reusing the lookup-only abstraction;
the new owner-hashed decoder rejects it. These tests use the actual service
bodies and retain memory between calls.

`PairRemoveRegion` proves three instructions in two fresh physical regions.
`PairRemoveOwnership.clear_ownership` connects the final NULL store to the
same ownership decoder used by the runner and to the source filter's target.
It does not prove bucket reconstruction through unlink or whole-function
removal adequacy. See the increment report for the explicit premises and limits.

The [index-subsystem increment](../docs/2026-10-18-paired-index-subsystem.md)
adds `PairUnlinkReconstruct` and `PairUnlinkOwnership`. They prove that the
combined concrete unlink stores restore the same executable reconstruction
and owner flags, deriving the list shape from successful decoding. Removal's
runner now checks the immutable storage separation used by these proofs.
`PairRemoveAdequacy.remove_checked` now composes the complete anchored
removal from the executable entry check, with ABI/callback readiness and a
physical frame. `PairRemoveEnvironment` exposes the sequential environment
and permission hypotheses. `PairRemoveWitness` proves linked/unhashed Pre
witnesses and specializes the execution theorem; `binary-pair-remove-witness`
executes their concrete states through return and repeated removal. Replacement
reconstruction and its paired runner are available; complete replacement and
actual captured mutator replay remain open. See the increment report for
commands, timing and the external export-based gate status.

For runtime diagnosis, `binary-pair-buffer-cost` uses a **generated variation**
of an allowed-IPs capture with a smaller KCOV allocation and changed capacity
metadata. It checks that the original instruction path is preserved under
both seeds and runs the same complete-call assertion. It is not unchanged
capture replay or a performance optimization of that replay. Given the capture
files prepared by the earlier capture recipe, run from the worktree root:

```sh
(cd binary && capped lake build binary-pair-buffer-cost)
capped binary/.lake/build/bin/binary-pair-buffer-cost \
  .tmp/cap-trie4/replay-input.json .tmp/cap-trie4/snapshot.json .tmp/cap-trie4/layouts.json
```

The original capture executable remains the unchanged-capture regression;
the diagnostic intentionally does not duplicate its independent captured
header/return comparisons or corruption controls. Do not substitute it for
that regression. All input/output captures, timing logs and leanexports are
ephemeral and should be regenerated and removed when no longer needed.
