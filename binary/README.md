# Binary adequacy and concrete probe

This is a standalone refinement experiment against the pinned **s5** Linux
image under explicitly unrealistic sequential/environment assumptions. It now
uses the split mirror through its actual adapters. The previous landing used
`task/binary-pair-landing`, rebased onto main `3308c49a`; the original experiment
branch is preserved. See the [landing report](../docs/2026-10-19-binary-landing-assessment.md)
for that landing's validation and the still-open milestone-1 review obligations.
The subsequent [allowed-IPs experiment](../docs/2026-10-20-binary-allowedips.md)
closes as partial component proofs and executable tests, with no new completed
function or insertion adequacy claim. Historical results below retain their
original commits and gate scope.

The package uses Lean v4.35.0, the mirror by path, and a private patched Kraken
checkout at `.deps/kraken`. Install the repository's Python dependencies
(including pyelftools) and the named Lean toolchain. From the checkout root:

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
cap python3 -B binary/run.py --bootstrap-only
cap lake -d binary build
scripts/binary-proof-gate
```

Bootstrap uses a staged shared upstream clone when available, otherwise the
locked upstream URL, and applies the committed patches with their exact Git
identities. It never repairs a dirty or differently pinned existing checkout.
A network fetch, if needed inside Nono, must be run outside Nono. Neither setup
nor the gate modifies machine-global configuration or requires the oracle ELF
for Lean compilation. The separate binary gate does not build `LeanuxProofs`.

The current semantics pin is `907830a1fb207e86f7914764717e3995c1f0df2d`:
upstream `8af78062037bc237b341d20252aafd1797c1bcb7` plus **nine** committed
patches. Patch [0009](kraken-patches/0009-register-bt.patch) adds the
register/register `bt` forms used at two sites in the pinned allowed-IPs
insertion image. It is retained because removing it would remove execution of
those paths and their tested segments. Register offsets are reduced modulo
the operand width; CF receives the selected bit, ZF and the registers are
preserved, and OF/SF/AF/PF are undefined. Unsupported operand forms fail closed.
The patch includes focused semantic tests, parser/printer roundtrips and a
native x86 comparison, plus the runner's missing Bool generator needed by
earlier ISA extensions. This is a **trust-surface change**, pinned consistently
in `dependencies/sources.lock.json` and `TrustBase.krakenCommit`; the tests do
not prove ISA fidelity. The closing report records its validation. No kernel
image change accompanies it.

Concrete tests and image comparison require the read-only s5 build. Set
`LEANUX_BINARY_KERNEL_DIR` to its directory; the default is
`.artifacts/kernel-net-choice-s5` in the common checkout. `binary/target.py`
verifies the exact ELF hash and selects `binary/kernel-identity-s5.txt` for
boots/captures. This is an explicit binary-package pin; it does not follow
future changes to the mirror campaign's oracle automatically.

The landing port moves from s4 because the current mirror requires B3
timer-wheel inputs absent from s4. Existing historical s4 results below
remain historical. The landing report records fresh s5 validation separately.
Image terms and DWARF offsets are regenerated from the new ELF; proof checking
then reestablishes the same claims at the relocated addresses. Compare the
committed generated files with the pinned image:

```sh
cap python3 -B binary/generate.py --check
cap python3 -B binary/generate_allowedips.py --check
cap python3 -B binary/generate_index_mutators.py --check
cap python3 -B binary/generate_random_service.py --check
cap python3 -B binary/generate_random_layout.py --check
```

The landing's combined export covers the original M1 transport and witnesses,
both-family physical Pre witnesses, the paired trie call, and the callback,
index and insertion headline closure. After the separate gate, from `binary/`:

```sh
cap lake env leanexport LookupSnapshotTransport LookupWitness LookupHitWitness \
  AllowedipsWitnessPre PairCallbackSurface PairCallWitness > ../.tmp/binary-pair-landing.ndjson
```

Require successful export generation. The external gate, run by the user
outside Nono from the same directory, is:

```sh
cap lake check --from-export ../.tmp/binary-pair-landing.ndjson
```

The exported closure avoids the checker's sandboxed build of parent path
dependencies. Fresh `leanchecker --fresh MODULE` replays and inside-Nono
checks are reported separately; neither replaces this external gate.

On 2026-10-19 the user ran this external gate outside Nono on the combined
export at code commit `736492453c292ba9caafa78b353ae19f4ce9671b`, covering
the six roots above and their complete declaration closure. The Lean default
kernel accepted it with only `propext`, `Quot.sound`, and `Classical.choice`.
The disposable export was removed after recording acceptance. Later changes
before this record affect only the Python identity preflight and documentation.
The theorem hypotheses and the landing report's open M1 obligations remain.

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

The executable reconstruction runners implement the
[paired-execution plan](../docs/2026-10-16-plan-executable-binary-correspondence.md#first-runnable-slice).
They preserve the existing M1 theorem and named hypotheses. From the current
checkout root, regenerate and run either recorded workload:

```sh
LEANUX_QEMU_SLOTS=16 cap python3 -B binary/pair_run.py --trace d1_second_response
LEANUX_QEMU_SLOTS=16 cap python3 -B binary/pair_run.py --trace d1_wrong_receiver_index_same_bucket
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
the new external gate. Fresh local kernel replay passes; the landing's combined
export also includes this generalization. The earlier boundary theorem does
not establish the later complete-call theorem described below.

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

Compatibility exception: `BinaryProofs.allowNonModules = true` deliberately
permits the legacy mirror modules and Kraken's new modules in this library.
Lean 4.35 rejects a new-style module importing the legacy mirror, while the
symbolic instruction proofs need Kraken definition bodies that its public API
does not expose. Migrating the mirror or changing Kraken's public API is outside
this experiment. This exception suppresses only Lake's import-style warning;
it does not suppress Lean proof, axiom, kernel-replay or simplifier diagnostics.
No file-wide Lean linter suppression is used.

All heavy commands run through `capped`; a KILLED banner or timeout fails.
The charter-authorized binary gate builds the default package, prints the
headline/witness axioms and checks proof sources for escapes. Before building,
it requires agreement between the lock, `TrustBase.krakenCommit`, the resolved
private path dependency and its clean Git HEAD (including untracked sources).
It prints the headline types, invocation-boundary definitions, R/postcondition
and verbatim trust declarations, and diffs `TrustSurface.expected.txt`:

```sh
capped -- scripts/binary-proof-gate
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

At this checkpoint the complete-call external gate was pending; the current
s5 carry is covered by the combined landing export accepted above. The earlier
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
executes their concrete states through return and repeated removal.
`PairReplaceAdequacy.replace_checked` and `PairReplaceEnvironment.replace_simulation`
likewise cover the complete replacement, including failure and all list
positions. `PairReplaceWitness` proves the linked/unhashed entry witnesses;
`binary-pair-replace-witness` executes their exact states and repeat calls.
`PairLookupAdequacy.lookup_checked` and its explicit-environment wrapper
now derive the older physical relation from the common executable assertion
and return the full reconstruction, ownership flags and callback phases.
`binary-pair-runner` checks that assertion around its existing segment runner.
`PairSequenceAdequacy.sequence_checked` proves arbitrary finite admissible
sequences from one checked initial state, with explicit caller setup and
retained heap/resources. `binary-pair-sequence` executes mixed sequences;
`sequence_probe.py` first runs all three independent function comparisons.
`capture_index_mutator.py` captures actual sequential entry/return memory for
both mutators, including unlinked argument roots and delisted but retained
peer allocations. `binary-pair-mutator-capture` runs their actual instructions
and compares every captured return byte, register, represented flag and PC.
Both captures pass under two seeds and focused corruption controls. Its source
input is reified from the captured entry projection; the recorded prefix
supplies identities and unobserved fields, not a claim of exact entry reachability.
See the increment report for capture/three-way commands and measured cost.

`PairSubsystemSurface` imports all seven new function/sequence headlines and
the removal/replacement formal entry witnesses. It prints their types and
axioms and the named trust premises. The existing `scripts/binary-proof-gate`
also prints and diffs these definitions and the full TrustBase specification.
From `binary/`, after a successful build, use:

```sh
capped lake build PairSubsystemSurface binary-pair-mutator-capture
capped lake env leanchecker --fresh PairSubsystemSurface
capped lake env leanexport PairSubsystemSurface > ../.tmp/binary-pair-index.ndjson
```

Require export exit status zero. The export is ephemeral and contains the
transitive declaration closure, including all three complete function proofs,
the sequence theorem, their executable definitions, both mutator witness
modules, TrustBase and Execution. The prepared export is from `fe596fd0b1d75a15801bf679657380676f61c0d6`;
its successful generation and validation status are recorded in the increment report. The external gate passed on 2026-10-18 for this commit; the
user runs this from `binary/` **outside Nono**:

```sh
capped lake check --from-export ../.tmp/binary-pair-index.ndjson
```

On 2026-10-18 the user reported acceptance by the Lean default kernel, using
only `propext`, `Quot.sound` and `Classical.choice`. This result is specific
to the named commit and complete `PairSubsystemSurface` closure above; it
does not cover later insertion work.


This avoids the sandbox's inability to resolve path dependencies. Fresh local
replay is not external acceptance. Delete the export after the external check;
regenerate captures and logs from their documented commands when needed.

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


## Insertion input-driven increment

The [insertion report](../docs/2026-10-18-paired-index-insertion.md) distinguishes
supplied random-service returns, captured native service transitions, and
Kraken-interpreted instructions. `Insert.insert_checked` proves full insertion
including reinsertion and arbitrary accepted collision prefixes.
`InsertSequence.sequence_checked` composes all four index functions over one
retained heap, deriving every next Pre and exporting reconstruction and input
consumption at every return. Both retain explicit service/environment hypotheses.
With the approved oracle selected, reproduce the first comparison from the
worktree root:

```sh
LEANUX_QEMU_SLOTS=16 capped scripts/in-bundle python3 -B -m evaluator.check \
  --suite wireguard --binary-coverage --binary-profile index-insert \
  --trace s2_index_collision --out .artifacts/check/binary-insert
(cd binary && capped lake build binary-pair-insert binary-pair-insert-capture binary-pair-insert-sequence)
capped scripts/in-bundle python3 -B binary/insert_probe.py \
  --check .artifacts/check/binary-insert
LEANUX_QEMU_SLOTS=16 capped scripts/in-bundle python3 -B binary/capture_index_mutator.py \
  --anchor insert --call-index 1 --input .tmp/binary-insert/input.json \
  --check .artifacts/check/binary-insert --operation 1 --out .tmp/cap-index-insert
capped scripts/in-bundle python3 -B binary/pair_insert_capture.py \
  .tmp/binary-insert/input.json .tmp/cap-index-insert/snapshot.json \
  .tmp/cap-index-insert/layouts.json
```

The Python interpreter must have the already documented ELF dependencies.
The replay driver verifies the current clean Kraken pin, oracle identity and
ELF hash against the capture before invoking Lean. The Lean entry point also
requires all three identities and checks them against its compiled pins.
Current captures include the private random/steering state and the dropped
record counter. The capture runner interprets the complete random bodies,
validates native REP multiplicities, and compares every captured endpoint byte
and represented register/flag under both undefined-value seeds. The old
segmented mode remains explicitly labelled and is not equivalent evidence.

After the three existing function comparisons and sequence preparation described
above, extend their input with insertion and run the retained-heap suite:

```sh
LEANUX_QEMU_SLOTS=16 capped scripts/in-bundle python3 -B binary/insert_sequence_probe.py \
  --base-input .tmp/binary-sequence/input.json --insert-input .tmp/binary-insert/input.json
(cd binary && capped lake build binary-pair-random-body binary-pair-insert-witness)
capped binary/.lake/build/bin/binary-pair-random-body
capped binary/.lake/build/bin/binary-pair-insert-witness .tmp/binary-insert/input.json
```

`PairInsertionSurface` extends the previous export root with both insertion
headlines, the mixed sequence theorem and the linked/unlinked formal witnesses.
The reviewed source is `5433d7781d9d809b82ea4c19faa13d40af9a4957`. From
`binary/`, after successfully building that source, reproduce the export with:

```sh
capped lake env leanchecker --fresh PairInsertionSurface
capped lake env leanexport PairInsertionSurface > ../.tmp/binary-pair-insert-reviewed.ndjson
# External gate, run by the user outside Nono:
capped lake check --from-export ../.tmp/binary-pair-insert-reviewed.ndjson
```

Require export exit status zero and record its exact source commit. The new
export was generated successfully on 2026-10-18 from the commit above, root
`PairInsertionSurface` and its full transitive closure. External acceptance
was pending at that checkpoint; the current s5 carry is covered by the combined
landing export accepted above. The previous `b3d57f17` insertion export is
superseded and its reconstructible file removed; earlier subsystem acceptance does not cover
the reviewed insertion source.

The [fresh insertion review](../docs/2026-10-18-review-paired-index-insertion.md)
found a private-state alias and missing replay identity checks. Both are repaired
and independently reviewed. The revised readiness assertion rejects the bad
alias without requiring disjoint capture blocks. Universal service and input
coupling contracts remain hypotheses. The
[checkpoint disposition](../docs/2026-10-18-paired-index-insertion.md#checkpoint-close-and-pause-2026-10-18)
records final validation and pause status. The original service-domain
counterexample remains in the review and executable regression. Captures,
exports and logs are ephemeral; regenerate them using the commands above.

## Shared image callbacks and first-return clients

The [bounded callback increment](../docs/2026-10-19-paired-callbacks.md) proves
KCOV PC, cmp4, const-cmp4, const-cmp1 and the ready BH-enable path directly
from the pinned decoded image. `PairCallbackSurface` imports their proofs and
the revised clients. `lookup_first_return`, `remove_first_return` and
`replace_first_return` retain the existing executable Pre/Post and export the
actual history, its first outer ABI return boundary, and its permission audit.
`Sequence.First.sequence_checked` retains that boundary for every call record.
These use `FirstReturnCallPermissions` / `FirstReturnDomainPermissions`.
Insertion's `insert_simulation_from_image` and mixed insertion sequences retain
the explicitly broader returning-history permission premise, and the random
service/input contracts. There is no concurrent-context claim.

Run the service tests and claim-point checks from `binary/`:

```sh
capped lake build PairCallbackSurface binary-callbacks
capped .lake/build/bin/binary-callbacks
capped lake env leanchecker --fresh PairCallbackSurface
capped lake env leanexport PairCallbackSurface > ../.tmp/binary-pair-callbacks.ndjson
# User gate outside nono; require successful export exit first:
capped lake check --from-export ../.tmp/binary-pair-callbacks.ndjson
```

The export contains the full imported declaration closure, including the older
index/insertion surfaces and witnesses. The prepared export is from code commit
`86ea5488e288998ea4aa0b26335c64428ffeaf04` and exited zero (1,331,952,229 bytes).
External acceptance was pending at that checkpoint; the current s5 carry is
covered by the combined landing export accepted above. Local check status is
recorded in the increment report. `scripts/binary-proof-gate`
prints and diffs the new statements and postcondition with the full
TrustBase specification and requires the pinned clean Kraken tree. The service
runner distinguishes generated cases from the recorded-prefix and captured
workload checks in the report. Tests do not discharge a universal contract.

## Allowed-IPs mutation scaling

Closed as an early experiment: [charter](../docs/2026-10-20-charter-binary-allowedips.md)
and [report](../docs/2026-10-20-binary-allowedips.md). The placement loop,
reassignment, root and child initialization/publication segments remain
buildable under the binary gate. Insertion is open; there is no new completed
function or subsystem adequacy claim. Run these from the worktree root, using
system Python with pyelftools (the QEMU command uses the project bundle when needed):

```sh
capped python3 -B binary/allowedips_mutation.py
LEANUX_QEMU_SLOTS=16 capped python3 -B - <<'PY'
import subprocess, sys
sys.path.insert(0, 'binary')
from target import ROOT, kernel_environment
subprocess.run([str(ROOT / 'scripts/in-bundle'), 'python3', '-B', '-m',
    'evaluator.check', '--suite', 'wireguard', '--no-build', '--binary-coverage',
    '--binary-profile', 'allowedips-insert', '--trace', 'b1_trie_routing',
    '--out', str(ROOT / '.artifacts/check/allowedips-insert-armed')],
    cwd=ROOT, env=kernel_environment(), check=True)
PY
capped python3 -B binary/allowedips_insert_check.py --check .artifacts/check/allowedips-insert-armed
LEANUX_QEMU_SLOTS=16 capped python3 -B binary/capture_allowedips_insert.py \
  --input .tmp/allowedips/mutation.json \
  --check .artifacts/check/allowedips-insert-armed \
  --out .tmp/allowedips/capture-first
capped lake -d binary build binary-allowedips-insert-capture
capped binary/.lake/build/bin/binary-allowedips-insert-capture \
  .tmp/allowedips/mutation.json .tmp/allowedips/capture-first/snapshot.json
```

Use unoccupied output directories for new recordings/captures. Build the mirror
first if it is not already built. The three-way comparison uses recorded calls
and outcomes with constructed entry memory. The separate capture replay uses
actual entry bytes, interprets WireGuard and coverage bodies, and supplies the
captured generic allocator transition under an explicit checked frame. Neither
test discharges a universal service premise. The sequence-counter reproducer
`capped python3 -B binary/allowedips_seq_wrap.py` preserves the Rule Zero
regression witness. It passes against the UInt64 mirror correction carried
from main `1f766662`, with the expected binary result unchanged.

The combined export for this experiment includes the earlier landing's roots
and the new lookup lift, common-bits reuse and partial insertion surface.
After the binary gate passes, from `binary/`:

```sh
capped lake env leanexport LookupSnapshotTransport LookupWitness LookupHitWitness \
  AllowedipsWitnessPre PairCallbackSurface PairCallWitness \
  PairAllowedipsLookupAdequacy AllowedipsCommonChecked AllowedipsInsertionSurface \
  > ../.tmp/binary-allowedips-landing.ndjson
# Require export exit zero; run the external gate outside Nono:
capped lake check --from-export ../.tmp/binary-allowedips-landing.ndjson
```

Earlier external acceptances do not cover these additions or patch nine.
`AllowedipsInsertionSurface` is a partial-proof replay root, not an insertion
adequacy theorem. The closing report distinguishes local checks from external
acceptance. The next direction is realization R1 of
`docs/2026-10-20-design-heap-view-overlay.md` on `task/design-heap-view`: an
executable typed heap view over unchanged Kraken semantics. That separate
increment begins only after this experimental landing.
