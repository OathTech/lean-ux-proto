# Replacement source-cut provenance pilot

The Python driver `replacement_source_capture.py` checks the actual entry's
record frontier before invoking the replacement admission executable. The
source observer executes the original caller and retains its exact hidden
record suffix. Neither the native heap nor the observed suffix supplies
replacement source values.

The bounded context is one replacement, ordinal zero, inside an uninterrupted
handshake receive-worker section [AGENT 2026-11-13]. This avoids guessing which
suspended activation resumed: the driver rejects overlapping open sections,
interleaved sections and rescheduling in the selected section prefix. Extending
that context requires a justified dispatch observer.

The driver checks the pinned native sequence-counter and dropped-record bytes,
the current task's PC-mode KCOV area, its actual section-start function/unit/
sequence, and every choice record in that area against the same boot's completed
records. It preserves stream and section provenance before sorting records by
sequence. The source remainder must equal the exact suffix after the native
frontier; passive records are never dropped to obtain a match. The source work
unit must also match the native section's unit.

The discovery capture's provenance check matched native frontier 47, section
start 40 and eight active-area records to source cursor 11 with 13 records
remaining. This is a provenance result; admission and full binary return replay
are separate checks that the driver runs afterward. The observed Device and
counters remain a WG slice, not a complete product-world observation. The
observer's enabled/disabled checkpoint comparison has the scope named in its
report, not extensional equality of function-valued world fields.

Build `binary-replacement-observe` and `binary-replacement-admit` in the binary
package using its documented private dependency setup. Capture with
`capture_index_mutator.py --anchor replace --operation 2 --call-index 0
--finish-workload` and the existing capture arguments, then run from the task
worktree (substitute the input and capture paths):
Select the host Python providing pyelftools before entering the bundle,
as in `binary/REPRODUCING.md`.

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
binary_python=$(command -v python3)
CAPPED_MEM_MAX=16G cap scripts/in-bundle "$binary_python" -B \
  binary/remediation/replacement_source_capture.py \
  --input .tmp/probe/input.json --capture .tmp/capture \
  --operation 2 --call-index 0
cap scripts/in-bundle "$binary_python" -B -m unittest discover -s binary -p 'test_*.py'
```

Failure in provenance, source execution or admission exits nonzero. Captures,
prepared inputs and result JSON are ephemeral; the driver removes its temporary
prepared input. The earlier completed-prefix diagnostic remains an unresolved
cut diagnostic and is not an alternative admission path.
