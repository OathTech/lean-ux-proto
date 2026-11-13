# Binary remediation: first implementation batch

Work on `feature/binary-remediation-20261113`, following the
[reviewed plan](2026-11-13-binary-remediation-plan.md). Implementation on a
feature branch was authorized [USER 2026-11-13]; neither main integration
nor publication is authorized. This report covers the plan's bounded first
batch, not completion of stages 1–6.

## What each part does

1. **Inventory the promises.** The existing
   [binary register](proofs.md#current-admission-inventory-2026-11-13) now
   names eight result groups, their entry/conclusion checkers, pins,
   scheduling scope and unresolved hypotheses. Historical proof acceptance
   remains tied to its original commit.
2. **Join lookup admission to execution.** Run the existing theorem's entry
   predicate and interpret the native call through its return on the same
   full-size captured memory. This tests whether a real invocation meets
   the stated local assumptions and returns as modeled. It cannot turn a
   finite sample into a universal service or kernel-caller theorem.
3. **Locate a mutator's source boundary.** Compare native replacement entry
   with original-mirror execution before and after the containing operation,
   using records from that same completed boot. This determines whether an
   existing observation point can justify the source state. Reconstructing
   that state from the binary heap cannot establish independent replay.
4. **Test the archived receive frame.** Observe count/register clauses and
   all physical RAM around clean-image C2 calls in ordinary and sequential
   modes, then test concrete virtual aliases. This distinguishes interference
   failures from a missing native-memory interpretation of the flat model.

The mirror, oracle images, theorem statements and Kraken semantics are
unchanged. C2 recovery consists of isolated observation tools; no archived
theorem or whole-driver target is adopted.

## Lookup implementation and resource diagnosis

The previous full-buffer replay was killed at both 12 and 32 GiB. Inspection
found that the lookup runner retained a full `MachineState` after every
instruction, although its consumers never read those snapshots. Kraken's
`DataMem` uses an array-backed persistent hash map; retaining versions can
force a large bucket-array copy on each store.

The bounded generated `binary/remediation/LookupHistoryCost.lean` diagnostic
uses a 256 KiB memory and the same 128 stores in both modes. Full retention
kept 129 states and used 2,248,368 KiB peak RSS; initial-only retention kept
one and used 1,692,716 KiB. Both retained all 128 write records and the same
final value. The approximately 543 MiB difference supports this mechanism.
It is not a native capture, an instruction-performance claim, or a definitive
post-mortem of the earlier kills.

The repair threads the interpreter's existing optional history selector
through `Pair.advance`, `lookupFrom` and `IndexLookup.runFrom`. Existing
clients keep their default. `PairCapture.run` selects initial-only history,
retaining every instruction PC/access and all live loop checks, and calls
the existing `IndexLookup.runFrom` instead of bypassing `callBoundary`.
The endpoint comparator reads captured bytes directly instead of building
a redundant expected memory map. Register widths, address bounds, byte
widths, flags, missing bytes and inconsistent overlaps still fail.

The collector now captures all 4,194,304 coverage words by default and the
checked replay refuses a partial allocation. Capacity and captured bytes
are unchanged; no memory representation or predicate is weakened.

Discovery hit and miss captures both pass the exact entry check and return
replay at both undefined-value seeds. Each checks 33,624,268 captured return
bytes, including the entire coverage allocation. Hit executes 506
instructions, miss 191. Peak process RSS is 8,095,336 / 8,096,276 KiB respectively,
under a 16 GiB job cap. Replay time is 208.721 / 186.244 seconds; the wrapper
including preparation takes 226 / 204 seconds. These are full-allocation
same-invocation results, unlike the earlier separate admission and
partial-buffer replay experiments.

After freezing the implementation at `6153f81a`, fresh hit and miss boots
also pass at both seeds, with the same instruction/byte/access counts.
Both repeat boots enter with count `0x80000000`, compared with `0` in the
discovery boots; these are observed values, not forced states. Their peak
process RSS is 8,117,996 / 8,117,068 KiB, replay time 208.261 / 224.073
seconds, and wrapper time 226 / 241 seconds. All four replay commands exit
zero under 16 GiB caps. This is two runs of each selected workload, not
broader workload or ordinary-scheduling coverage.

This conjunction still excludes universal permissions and the transport
theorem's initial keypair/frontier representation and global separation.
The current lookup collector does not capture the global keypair counter
and refuses keypair identity setup. The exact `Pre` plus instruction/return
checks are a scoped admission result, not admission of every older headline
premise or the full native frame.

## Replacement and C2 boundaries

The [source-cut experiment](2026-11-13-replacement-source-cut.md) ran one
discovery and one held-out replacement capture, with different recorded
index draws. Each preserves 115 native instructions and then completes all
six workload operations. Neither neighboring completed-operation source
state equals native entry; the later state's index projection matches
native return. Both diagnostics exit **2: unresolved source cut**. The
report proposes a read-only observation of the original mirror immediately
before the actual replacement call, carrying arguments, state, record
cursor and remaining records through the same continued execution. That
observer is not implemented by this batch.

The [C2 report](2026-11-13-c2-native-frame.md) records 32 final ordinary and
32 final sequential visits. Ordinary execution fails the exact count and
physical-frame clauses at four visits, including IRQ-stack writes. The
sequential visits pass those two finite checks. Both modes exhibit a
changed direct-map alias outside the statement's virtual footprint on all
32 visits. Both checker commands correctly exit **1**. C2 is **not
admission-ready**.

The next C2 candidate must declare a native-to-model memory projection and
justify that relevant loads, stores and caller observations respect it.
A physical-footprint frame differs from preservation of every native
virtual byte. Ordinary execution additionally needs an interference model.
Lifetime reuse and hand-overs remain separate work. These are proposed
statement boundaries [AGENT 2026-11-13], not admitted replacement claims.

## Validation scope

The binary default build and 71-headline trust gate pass with standard
axioms and an unchanged printed surface. Fresh kernel replay of the
`PairCapture` import closure passes. The lookup image/layout generator
passes against the saved ELF. The final binary Python suite passes 23 tests;
six C2 unit controls also pass. The streaming endpoint diagnostic accepts
consistent overlaps and rejects eight malformed/changed endpoints.
Both constructed lookup suites pass 48 calls and 18 negative controls each,
including the new missing-last-coverage-byte check. These generated cases
are distinct from native admission.

The model/fixed-width build and 149 mirror/harness unit tests pass, with one
existing skip. Two independent lookup differential recordings pass 14
operations in total. The source-cut worker additionally reports a successful
six-operation differential recording. Worker reports document their setup
failures and corrected collector/diagnostic issues; no semantic mismatch
was retried into a pass.

No new proof or external export acceptance is claimed. Full mirror suites,
controls and sentinels have not been rerun for this bounded binary-only
batch; they remain required at a later mirror integration claim point.
The mirror proof register's existing lag is unchanged.

## Independent review and disposition

The independent implementation review checks this batch separately from
the earlier plan reviews. Its report is
[here](2026-11-13-review-binary-remediation-implementation.md). The reviewer
independently builds the relevant code, runs the Python and endpoint
controls, and compares full versus limited history on generated hit/miss
fixtures. At both seeds, the final machine/source projections, PCs,
accesses, comparisons and coverage match; retained states change from
507/192 to one. Read-only inspection confirms the discovery captures'
complete coverage blocks and return extents. C2 raw captures were already
removed, so that part is a source/unit review, not an independent native
rerun.

The reproduction finding is fixed: the commands now explicitly verify the
s5 ELF and select its directory and identity for the recording harness.
The actual completed recordings already have the checked s5 identity and
ELF hash. This was a recipe defect, not a reason to relabel the successful
recordings. No broader admission or integration approval follows from the
review.

## Reproduce the lookup experiment

Prerequisites and saved-image limitations are in
[binary/README.md](../binary/README.md). From the feature worktree, select
the host Python before entering the bundle. Set `LEANUX_BINARY_KERNEL_DIR`
to the saved s5 build directory and select that checked image for the
recording harness too, as in [the execution recipes](../binary/REPRODUCING.md):

```sh
binary_python=$(command -v python3)
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
: "${LEANUX_BINARY_KERNEL_DIR:?Set this to the saved s5 build directory}"
export LEANUX_BINARY_KERNEL_DIR
binary_identity=$("$binary_python" -c 'import sys; sys.path.insert(0, "binary"); from target import pins, verify_image; verify_image(); print(pins()[0])') || exit 1
export LEANUX_KERNEL_DIR="$LEANUX_BINARY_KERNEL_DIR"
export LEANUX_KERNEL_IDENTITY="$binary_identity"
CAPPED_MEM_MAX=8G cap scripts/in-bundle "$binary_python" -B binary/run.py --bootstrap-only
CAPPED_MEM_MAX=8G cap scripts/in-bundle lake build leanux-model leanux-fixed-width-tests
CAPPED_MEM_MAX=16G cap scripts/in-bundle "$binary_python" -B scripts/binary-proof-gate
```

These environment settings are local to the experiment shell. Use a fresh
shell or restore the normal mirror oracle before running mirror comparisons.

For each of `d1_second_response` (hit) and
`d1_wrong_receiver_index_same_bucket` (miss), set `lookup_trace` and a short,
fresh `lookup_out`, then run:

```sh
lookup_trace=d1_second_response
lookup_out=.tmp/lookup-hit
CAPPED_MEM_MAX=8G cap scripts/in-bundle "$binary_python" -B -m evaluator.check \
  --suite wireguard --no-build --binary-coverage --binary-profile index \
  --trace "$lookup_trace" --out ".artifacts/check/$lookup_trace"
CAPPED_MEM_MAX=12G cap scripts/in-bundle "$binary_python" -B binary/pair_run.py \
  --trace "$lookup_trace" --check ".artifacts/check/$lookup_trace"
CAPPED_MEM_MAX=8G cap scripts/in-bundle "$binary_python" -B binary/capture_lookup.py \
  --input ".tmp/binary-pair/$lookup_trace/input.json" \
  --check ".artifacts/check/$lookup_trace" --out "$lookup_out"
CAPPED_MEM_MAX=16G cap scripts/in-bundle "$binary_python" -B binary/pair_capture.py \
  --capture "$lookup_out" --check ".artifacts/check/$lookup_trace"
```

The independent recording prepares the invocation; the source prefix used
by captured replay comes from the capture's own boot. Repeat the last two
commands with a fresh output directory for another boot. Large snapshots
and logs are ephemeral; remove the named output directories after recording
the result.

The generated diagnostics are separate from captured admission:

```sh
CAPPED_MEM_MAX=4G cap scripts/in-bundle lake -d binary env lean --run \
  binary/remediation/CaptureEndpointChecks.lean
CAPPED_MEM_MAX=4G cap /usr/bin/time -v scripts/in-bundle lake -d binary env lean --run \
  binary/remediation/LookupHistoryCost.lean all
CAPPED_MEM_MAX=4G cap /usr/bin/time -v scripts/in-bundle lake -d binary env lean --run \
  binary/remediation/LookupHistoryCost.lean none
```
