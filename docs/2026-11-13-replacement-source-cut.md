# Replacement: the source cut is still unobserved

Historical first-batch diagnosis. The later
[source-entry observer](2026-11-13-replacement-observer.md) implements the
interface proposed below and reports its separate validation and limits.

Conclusion and proposed next interface [AGENT 2026-11-13]. This is the
source-alignment investigation from the first batch of the
[remediation plan](2026-11-13-binary-remediation-plan.md), over mirror
`9ca4b0655d8a` and the unchanged s5 image/semantics pins. No operational
mirror definition or theorem is changed.

## Result

The existing completed-operation replay cannot supply the source entry
state of the selected index replacement. A fresh same-boot diagnostic
demonstrates that the states on either side of the containing operation
are different from the native function's entry. This is **unresolved caller
alignment**, not a mirror counterexample and not a reason to replace the
expected source state with captured values.

For `c_remove_after_handshake`, the selected native replacement occurs
inside operation 2, after operations 0 and 1 have completed. The existing
`replace_probe.py` deliberately prepares `input.operation = 3`, giving
`MutatorCapture.names` the keypair allocation identity from the completed
containing operation. The current replay then constructs its local source
input from the captured projection. Its documented local state-input
claim is different from predicting the caller's entry independently.

The source order explains the gap. `beginSession` in
`Leanux/WG/Handshake.lean` allocates and initializes the keypair, derives
its keys, clears the handshake and calls `addNewKeypair` before calling
`indexReplaceHandshake`. The completed-operation prefix before that work
is too early; the prefix after it is too late.

Both the discovery and held-out boots exhibit the following projection:

| Boundary | Index table | Keypair allocation |
| --- | --- | --- |
| Original mirror after two completed operations | Empty | None |
| Captured replacement entry inside operation 2 | Handshake owner at the recorded index | Internal ID 1 already exists |
| Captured replacement return | Keypair owner at that same index | Internal ID 1 |
| Original mirror after three completed operations | Keypair owner at that same index | Internal ID 1 |

Neither completed-operation table equals the native entry table. The
native return table equals the completed-operation source table. That last
equality concerns this projection only; it does not establish complete
world equality, caller alignment or a new hand-over theorem.

## What changed

`binary/capture_index_mutator.py` gains an opt-in `--finish-workload` mode.
It first preserves the same entry, executed-PC list and return snapshots
as before. It then detaches the debugger and lets the same guest finish,
checking every operation, one successful batch, successful guest exit and
the QEMU exit code. Failure remains a failed capture. The default mode
still stops after the selected function. The new mode changes neither the
captured bytes nor the saved endpoint and does not observe all later caller
instructions.

This continuation is necessary because the containing operation's hidden
records are emitted only after that operation returns. It supplies those
records from the same boot rather than borrowing them from an independent
run. The full guest also executes a separate comparison-mode trial; the
diagnostic explicitly selects the PC-mode trial in which the snapshot was
taken and rejects unknown modes. It never combines the two trials' records.

`binary/remediation/ReplacementPrefixes.lean` calls the existing
`replayRecordedPrefix` on those records at the two completed-operation
boundaries. It contains no reimplementation of the handshake or mutator
control flow. `replacement_prefix_diagnostic.py` compares the resulting
index projections with the captured native entry/return. Public keys and
keypair allocation counters label objects; captured table values are never
inputs to source execution.

The diagnostic returns **exit 2**, with `status = unresolved-source-cut`
and `source_cut_observed = false`, even if one projection happens to match.
It is not an admission checker. Missing completion, wrong identity or
malformed input produces a different nonzero failure rather than a partial
result. The supplied source prefix and snapshots remain ephemeral.

## Validation

The mirror executable builds in 130 jobs and `ProbeSupport` in 81 jobs.
The new Lean diagnostic elaborates without warnings. The binary Python
test suite passes all 23 tests, including new completion/error tests and a regression
that keeps the later comparison-mode records out of the PC-mode prefix.

One fresh independent differential recording passes: one workload, six
operations, 73 matched operand pairs and 44 distinct operand rows. The
discovery and held-out native captures each record 115 replacement
instructions and 33,625,500 entry bytes, then complete all six operations
successfully. The recorded random index is 3213607472 in discovery and
4178527354 in the held-out boot. Each source replay uses its own boot's
records and consumes them completely at both completed-operation boundaries.
Both diagnostics exit 2 with the unresolved cut shown above: entry differs
from both neighboring source tables, while return matches the later table.

The first diagnostic invocation rejected the completed guest's later
comparison-mode records. The phase selector was corrected to retain only
the PC trial, with an unknown-mode rejection test, before the held-out boot.
No failed model execution was retried and no capture was repaired.

No source-cut theorem, caller proof, ordinary-scheduling claim or full
binary return replay is added by this task. The observation of 115 native
instructions is a capture count, not an assertion that they were replayed
under Kraken here.

## Missing capability and concrete next observer

`WG.M` and `IndexM` are `StateT` computations over `AmbientM`, which itself
uses `Except Stop`. The public runner returns the completed state; a stop
does not return an intermediate world. The existing `Step` log contains
decisions and comparison operands, not the current WG store or hidden
stream position. `IndexM` sees the table and ambient state, not the whole
WG store needed to name the freshly created keypair and the owner fields.
There is no existing hook that exposes the required conjunction at this
call boundary.

The proposed next work unit is a narrowly scoped, read-only source
observation interface, with these requirements:

1. Observe the actual original `beginSession` execution immediately before
   its call of `indexReplaceHandshake`, with the actual arguments and WG
   state. Preserve the current ambient record cursor, remaining records
   and dispatch identity. Any product-world components needed by the
   chosen predicate must come from the containing execution as well.
2. Identify the observation by operation, PC/comparison trial, function
   and ordinal within that operation. Match allocation lifetimes through
   their existing identity records, rather than selecting a convenient
   state by comparing its values with the native snapshot.
3. Continue the same source execution. Observations are append-only output
   and cannot influence branch decisions, record consumption or state
   updates. A missing or duplicated requested observation is an explicit
   failure; there is no completed-prefix fallback.
4. Check that observation enabled/disabled preserves normal results and
   record consumption, then check the actual entry predicates on a fresh
   native capture. Preserve the distinction between an observed WG slice
   and a complete product-world claim.

This requires a reviewed observation point at the subsystem/caller
boundary, not simply another CLI switch on `replayRecordedPrefix`.
Manually copying the front of `beginSession`, fitting state from the native
heap, or interpreting the post-operation world as its pre-call world would
recreate the original specification problem. A general new interpreter,
proof-generating source rewriter, or broad monad redesign is not part of
this bounded investigation.

The observer is a proposal, not an implemented capability. Until it exists
and the full chosen predicates pass, retain the current local state-input
result and leave independent caller admission unresolved. Do not commission
a proof or composition that assumes this missing cut has been supplied.

## Reproduction

Use a task worktree, the saved s5 image and the setup in
`binary/README.md` and `binary/REPRODUCING.md`. Select the image environment
there before the recording command. No new kernel or dependency pin is
needed. With a Python interpreter that provides pyelftools:

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
binary_python=$(command -v python3)
cap scripts/in-bundle "$binary_python" -B binary/run.py --bootstrap-only
cap scripts/in-bundle lake build leanux-model
cap scripts/in-bundle lake -d binary build ProbeSupport
cap scripts/in-bundle "$binary_python" -B -m evaluator.check --suite wireguard \
  --no-build --binary-coverage --binary-profile index-replace \
  --trace c_remove_after_handshake --out .artifacts/check/source-cut
cap scripts/in-bundle "$binary_python" -B -c '
from pathlib import Path
import sys
sys.path.insert(0, "binary")
from remove_probe import prepare
prepare(Path(".artifacts/check/source-cut").resolve(),
        Path(".tmp/source-cut/probe"), "wg_index_hashtable_replace", 3)
'
CAPPED_MEM_MAX=16G cap scripts/in-bundle "$binary_python" -B binary/capture_index_mutator.py \
  --anchor replace --input .tmp/source-cut/probe/input.json \
  --check .artifacts/check/source-cut --operation 2 \
  --out .tmp/source-cut/discovery --finish-workload
CAPPED_MEM_MAX=8G cap scripts/in-bundle "$binary_python" -B \
  binary/remediation/replacement_prefix_diagnostic.py \
  --input .tmp/source-cut/probe/input.json --capture .tmp/source-cut/discovery
```

The last command should report the unresolved source cut and exit 2; do
not turn that into an admission pass. Repeat the capture with a fresh
output directory for the held-out boot. Remove the captures, records and
private build outputs when the conclusion is recorded.
