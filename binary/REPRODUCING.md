# Binary execution recipes

This is the detailed companion to [the binary overview](README.md), which
states the claims, prerequisites and trust checks. These commands require
the saved s5 ELF, a bootstrapped binary package, Python with pyelftools and
the mirror's staged tool bundle. They cannot be reproduced from the Git
clone alone. No successful rerun is asserted by listing a command here.

Run from a task worktree's root. Keep `binary_python` set to the interpreter
selected in the overview, and set `LEANUX_BINARY_KERNEL_DIR` to the saved s5
build directory. Define the `cap` helper, then select the binary package's
image and identity for this shell only:

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
: "${LEANUX_BINARY_KERNEL_DIR:?Set this to the saved s5 build directory}"
binary_identity=$("$binary_python" -c 'import sys; sys.path.insert(0, "binary"); from target import pins, verify_image; verify_image(); print(pins()[0])') || exit 1
export LEANUX_KERNEL_DIR="$LEANUX_BINARY_KERNEL_DIR"
export LEANUX_KERNEL_IDENTITY="$binary_identity"
```

The identity command refuses a different ELF. These settings are for the binary experiment. Use a fresh shell, or unset
`LEANUX_KERNEL_IDENTITY` and restore the current `LEANUX_KERNEL_DIR`, before
returning to normal mirror comparisons.

Each output directory must be unused. Replace the indicated recording paths
with the successful run produced by the preceding command. Build the model
first if needed (`cap scripts/in-bundle lake build leanux-model`). Select a
Python interpreter with pyelftools before entering `scripts/in-bundle`; its
Python environment may differ from the host's.

## Index lookup: recorded and constructed states

Run both workloads from the root. The driver records kernel behavior first,
then compares it with the mirror and constructed entry heaps under Kraken.
These heaps are not captured kernel memory.

```sh
LEANUX_QEMU_SLOTS=16 cap scripts/in-bundle "$binary_python" -B binary/pair_run.py --trace d1_second_response
LEANUX_QEMU_SLOTS=16 cap scripts/in-bundle "$binary_python" -B binary/pair_run.py --trace d1_wrong_receiver_index_same_bucket
```

## Allowed-IPs lookup: constructed states

The generated inputs exercise IPv4 and IPv6. The independent differential
recording produced by the probe is also the CHECK_DIRECTORY needed below.

```sh
LEANUX_QEMU_SLOTS=16 cap scripts/in-bundle "$binary_python" -B binary/allowedips_probe.py --budget 100000
(cd binary && cap ../scripts/in-bundle lake build binary-pair-allowedips)
cap binary/.lake/build/bin/binary-pair-allowedips .tmp/binary-allowedips/input-5.json
cap binary/.lake/build/bin/binary-pair-allowedips .tmp/binary-allowedips/input-8.json
```

## Allowed-IPs lookup: captured states

Replace CHECK_DIRECTORY with the successful recording from the previous
step. This captures actual entry, header and return bytes. Use input-8.json
and a fresh output directory for IPv6. Keep snapshot sidecars with their JSON.
The replay defers interrupts and timers inside the call: it tests a sequential
environment, not ordinary concurrent kernel execution.

```sh
capture_python="$binary_python"
LEANUX_QEMU_SLOTS=16 cap scripts/in-bundle "$capture_python" -B binary/capture_allowedips.py \
  --input .tmp/binary-allowedips/input-5.json --check CHECK_DIRECTORY --out .tmp/captured-trie4
cap scripts/in-bundle "$capture_python" -B binary/pair_allowedips_capture.py \
  --capture .tmp/captured-trie4 --check CHECK_DIRECTORY
```

## Index lookup: captured states

Replace the recording path with the successful d1_second_response recording.
The sequential replay compares captured registers, bytes and instruction
history. Ordinary-scheduling captures are diagnostic only and are refused by
this replay.

```sh
LEANUX_QEMU_SLOTS=16 cap scripts/in-bundle "$binary_python" -B binary/capture_lookup.py \
  --input .tmp/binary-pair/d1_second_response/input.json \
  --check CHECK_DIRECTORY --out .tmp/captured-lookup \
  --execution-mode sequential
cap scripts/in-bundle "$binary_python" -B binary/pair_capture.py \
  --capture .tmp/captured-lookup --check CHECK_DIRECTORY
```

## Index insertion: recorded and captured states

These commands use the s5 identity selected at the start of this guide.
The recorded-prefix comparison and actual capture are separate checks.

```sh
LEANUX_QEMU_SLOTS=16 cap scripts/in-bundle python3 -B -m evaluator.check \
  --suite wireguard --binary-coverage --binary-profile index-insert \
  --trace s2_index_collision --out .artifacts/check/binary-insert
(cd binary && cap ../scripts/in-bundle lake build binary-pair-insert binary-pair-insert-capture binary-pair-insert-sequence)
cap scripts/in-bundle "$binary_python" -B binary/insert_probe.py \
  --check .artifacts/check/binary-insert
LEANUX_QEMU_SLOTS=16 cap scripts/in-bundle "$binary_python" -B binary/capture_index_mutator.py \
  --anchor insert --call-index 1 --input .tmp/binary-insert/input.json \
  --check .artifacts/check/binary-insert --operation 1 --out .tmp/cap-index-insert
cap scripts/in-bundle "$binary_python" -B binary/pair_insert_capture.py \
  .tmp/binary-insert/input.json .tmp/cap-index-insert/snapshot.json \
  .tmp/cap-index-insert/layouts.json
```

## Allowed-IPs mutation scaling

These test the unfinished mutation experiment. The first runner uses
constructed states; the capture replay uses actual entry bytes and a supplied
allocator transition under an explicit checked frame. Neither proves whole
insertion or a universal allocator contract.

```sh
cap scripts/in-bundle "$binary_python" -B binary/allowedips_mutation.py
LEANUX_QEMU_SLOTS=16 cap scripts/in-bundle "$binary_python" -B - <<'PY'
import subprocess, sys
sys.path.insert(0, 'binary')
from target import ROOT, kernel_environment
subprocess.run([str(ROOT / 'scripts/in-bundle'), 'python3', '-B', '-m',
    'evaluator.check', '--suite', 'wireguard', '--no-build', '--binary-coverage',
    '--binary-profile', 'allowedips-insert', '--trace', 'b1_trie_routing',
    '--out', str(ROOT / '.artifacts/check/allowedips-insert-armed')],
    cwd=ROOT, env=kernel_environment(), check=True)
PY
cap scripts/in-bundle "$binary_python" -B binary/allowedips_insert_check.py --check .artifacts/check/allowedips-insert-armed
LEANUX_QEMU_SLOTS=16 cap scripts/in-bundle "$binary_python" -B binary/capture_allowedips_insert.py \
  --input .tmp/allowedips/mutation.json \
  --check .artifacts/check/allowedips-insert-armed \
  --out .tmp/allowedips/capture-first
cap scripts/in-bundle lake -d binary build binary-allowedips-insert-capture
cap binary/.lake/build/bin/binary-allowedips-insert-capture \
  .tmp/allowedips/mutation.json .tmp/allowedips/capture-first/snapshot.json
```

## Other experiments

[Index removal, replacement and retained-heap composition](../docs/2026-10-18-paired-index-subsystem.md)
has the function-comparison and capture commands. The
[index insertion report](../docs/2026-10-18-paired-index-insertion.md) supplies
the sequence preparation and exact witnesses. The
[callback report](../docs/2026-10-19-paired-callbacks.md) covers bounded callback
tests and first-return clients.

Return to [the binary trust checks](README.md#check-the-proof-boundary) for
export and external replay. Passing an executable test does not replace
those checks or discharge the theorem premises. Captures, logs and exports
are temporary outputs: remove the specific run directories after use.
