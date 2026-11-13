# C2: native frame observation and the remaining representation boundary

First-batch investigation [AGENT 2026-11-13], under
[the remediation plan](2026-11-13-binary-remediation-plan.md), stage 3.
The result is a concrete frame/projection finding and a small executable
observer, **not admission of the complete C2 statement or a repaired proof**.
No mirror, theorem, kernel, guest behavior or default s5 target is changed.

The statement examined is `Binary.Rt.C2.Kept` in
`archive/whole-driver-pilot-2026-11-12` (`8b498e7ec207`),
`binary/RtC2Statement.lean`. Its count equation adds `0x200` modulo
32 bits. Its frame is `EqualOutside (Footprint kp)`, where the footprint is
the 1,032 window bytes at `kp + 136` and four bytes at
`0xffffffff818c8588`. The range is the clean image's 37-instruction C2 cut.

## What was run

The new `binary/remediation/c2_capture.py` uses the existing debugger
transport with a read-only monitor extension. A guest is prepared by the
archived `binary/workloads/two_device.py`. The observer checks the exact
clean-image identity and ELF hash, the guest's CPU/single-CPU/RAM settings,
and the live C2 bytes against the ELF. The main package's s5 selection is
unchanged; no archived theorem or full target switch is imported.

For each of the first 32 C2 visits it records entry and exit registers,
window/nonce/count bytes, the actual CR3, a direct debugger read of the
count's other virtual alias, and **all 256 MiB of physical RAM**. RAM is
stored as complete initial data followed by checked page deltas. Both
debugger reads and the live code are cross-checked against the RAM images
using the captured page-table root.

Two separate modes were tested without forcing any register or guest byte:

* `sequential` steps every range instruction with QEMU's IRQ/timer-deferred
  mode 7, recording the executed PCs;
* `ordinary` resumes between the entry and exit breakpoints. As in the
  existing archived capture, stepping over a breakpoint defers interrupts
  for that one instruction. Stops and RAM observations affect timing; this
  is an instrumented naturally scheduled execution, not an unobserved run.

Both final boots completed the workload marker, exited QEMU successfully,
and captured 32 visits with no stray exit stops, yielding 64 RAM snapshots
per mode. The collector removes the three breakpoints after the selected
32 visits. This is bounded evidence about individual calls, not full
workload or lifetime/hand-over coverage. No claim is made about visits
after that boundary or about network outcomes beyond obtaining the visits.

## Results of the final captures

`c2_check.py` exits **1** on both captures, with explicit failed conjuncts.
It never labels the complete Lean statement admitted.

| Observation | Ordinary scheduling | Sequential stepping |
| --- | ---: | ---: |
| Visits checked | 32 | 32 |
| Exact count equation failures | 4 | 0 |
| Kept-register / unlock-argument failures | 0 | 0 |
| Physical-footprint frame failures | 4 | 0 |
| Changed physical bytes outside the footprint, total | 1,560 | 0 |
| Counterexamples to the literal all-native-virtual-byte frame | 32 | 32 |

The ordinary count/physical-frame failures occur at visits 13, 19, 22 and
23. For example, an entry count `0x80000101` produces `0x301`, whereas
`Kept.count` requires `0x80000301`. Extra physical writes include
`irq_stack_backing_store`; the first failing visit changes 377 bytes
outside the physical image of the stated footprint. This is expected
interrupt activity that the sequential instruction model does not cover,
not a newly alleged kernel bug. No retry was used to remove these failures.

The physical-frame check compares every captured RAM byte, allowing only
the physical images of the stated window/count addresses. All their
translations must remain unchanged during the visit. The sequential result
therefore establishes this finite physical-memory observation for these
32 invocations. It does not establish a virtual-address frame or an
universal claim about other invocations.

## Why the virtual frame also needs attention without interrupts

The count's image address `0xffffffff818c8588` and its direct-map alias
`0xffff8880018c8588` address the same physical word. The latter is outside
`Footprint kp` in these visits. On the first visit in each mode, for
example, the byte at virtual address `0xffff8880018c8589` changes from
`0x01` to `0x03`; the physical address is `0x18c8589`. Its translation is
checked in both endpoint RAM images through the actual CR3. The collector
also reads this alias directly through the debugger at both endpoints.

Thus the native virtual view changes at an address outside the statement's
virtual footprint. This happens on **every** captured visit in both modes.
No interrupt, changed write set or inferred alias is needed for this
counterexample. The checker searches the image/direct-map aliases and
reports concrete changed bytes; absence of a found counterexample would
remain unresolved, not a frame pass over every virtual address.

This does **not** refute the Lean theorem. Kraken's flat `DataMem` is not
a native paged memory with automatically coherent aliases. A state
containing only selected canonical addresses can satisfy the proved frame.
But interpreting it as preservation of every native virtual byte is false.
The native-to-model memory projection and its observation domain must be
part of an applicability claim, rather than silently omitted by sparse
capture. A pass of the physical-footprint check is a different predicate.

## Concrete proposed next statement boundary

The useful next experiment is a **declared projection**, fixed before its
test, rather than enlarging `Footprint` from the observed differences:

1. Name the native observation domain and choose how model addresses denote
   native memory. For a sequential local claim, the present all-RAM
   physical-footprint observation is executable. A canonical virtual
   projection is another option, but must state which aliases it omits.
2. Require stable translations and justify that model loads and stores
   commute with that projection for every accessed location. Address
   aliasing and the caller's ownership interpretation are part of this
   obligation; finite passing samples do not prove it.
3. Check that every byte the caller needs framed is included in the domain.
   A small sparse snapshot cannot discharge a frame over unobserved memory.
   If the domain is restricted, retain that restriction in the result and
   in every proposed hand-over.
4. For ordinary scheduling, describe and capture the intervening environment
   transitions and their permitted effects. Do not hide the IRQ-stack
   writes or simply allow the reschedule bit to change. The observed four
   failures are regression examples, not an exhaustive interference model.

This investigation supplies no such projection proof or environment model.
It returns the proposed boundary for review. Source refinement, complete
instruction semantics, unobserved aliases/non-RAM domains and allocation
lifetimes remain unchecked. The workload's in-order visits do not supply
the planned duplicate/boundary/reallocation cases, so C2 is **not
admission-ready** for new proof or composition.

## Validation and reproduction

Six small unit controls passed: complete-base/delta reconstruction,
physical changes outside the permitted footprint, alias visibility,
unmapped/out-of-RAM reads, and rejection of the cleared-reschedule-bit
alternative. A one-off mutant which suppressed every alias check was
rejected by the alias control; the mutant was removed.

The two discovery boots each obtained 32 paired snapshots and reached the
workload's completion marker, but the collector failed at QEMU shutdown
while acknowledging the final debugger packet. Those runs are not counted
as successful capture commands. The collector now accepts that connection
closure only if QEMU exits zero and the workload completion marker is
present. The two final runs above test that correction and the additional
CR3/direct-alias instrumentation. Before any sequential discovery boot,
parallel initialization of the private tool bundle also failed once; that
startup was retried once after initialization. No shared state was repaired
or modified, and no model mismatch was retried.

Prerequisites are the saved clean ELF/kernel and the ordinary binary
capture dependencies. The archive is used only to prepare the existing
workload. For example, from the feature worktree:

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
binary_python=$(command -v python3)
git worktree add ../c2-input -b task/c2-input archive/whole-driver-pilot-2026-11-12
(cd ../c2-input && LEANUX_BINARY_TARGET=net-clean-2 CAPPED_MEM_MAX=8G \
  cap scripts/in-bundle "$binary_python" -B binary/workloads/two_device.py \
  --out .artifacts/c2-input --prepare-only)
CAPPED_MEM_MAX=8G cap scripts/in-bundle "$binary_python" -B \
  binary/remediation/c2_capture.py \
  --command ../c2-input/.artifacts/c2-input/qemu-command.json \
  --out .tmp/c2-ordinary --mode ordinary --first 32
CAPPED_MEM_MAX=4G cap "$binary_python" -B binary/remediation/c2_check.py .tmp/c2-ordinary
```

The last command is expected to fail the native virtual frame; report its
JSON and exit status as a failure. Use a fresh output directory and
`--mode sequential` for the other experiment. Ordinary scheduling may
produce different interrupt counts. A run with no interruptions would
not erase the existing counterexamples.

```sh
CAPPED_MEM_MAX=1G cap "$binary_python" -B -m unittest discover \
  -s binary/remediation -p 'test_c2_memory.py'
```

`c2_capture.py` is a collector and reports `captured`, not a proof verdict.
`c2_check.py` reports failure on observed counterexamples and incomplete
otherwise; neither result is silently converted to success. Raw snapshots,
logs and the preparation worktree are ephemeral and are removed after
recording these conclusions. No new Lean proof or external kernel
acceptance is claimed for these Python observation helpers.
