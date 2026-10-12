# Linux test runner

The harness executes JSON operation traces in QEMU and collects Linux results
and coverage. For a comparison with the Lean model, use
[`evaluator.check`](../REPRODUCING.md); this runner collects only the Linux side.

## Run a trace

Complete the [setup](../REPRODUCING.md) and export `LEANUX_KERNEL_DIR` to the
matching `net-choice` build. From your worktree:

```sh
mkdir -p .tmp
python3 -c 'import json; print(json.dumps(json.load(open("corpus/handwritten/alias_close.json"))))' > .tmp/alias_close.jsonl
capped -- scripts/in-bundle python3 -m harness.linux .tmp/alias_close.jsonl --out .artifacts/run-alias-close
```

Input is JSONL: one complete trace per line. Corpus `.json` files are formatted
across multiple lines, hence the conversion above. The output directory must
be new or empty and inside the worktree's `.artifacts/` (or `LEANUX_ARTIFACTS`
if configured). Choose a new directory for another run. `--timeout` sets the
guest timeout in seconds; the default is 120.

The Python entry point is `harness.linux.run_linux(traces, outdir, timeout=120)`.
It returns observation objects in input order and raises `LinuxRunError` for
build, guest, coverage, output, timing or resource failures.

## What runs where

The host compiles `guest.c` and builds an initramfs. It verifies the pinned
kernel's identity before booting a fresh VM, using single-threaded TCG, one
x86-64 CPU and 256 MiB RAM. The VM has no external network device, shared host
filesystem or host disk. Experimental syscall sequences run only in the guest;
the harness never rebuilds the kernel.

Each trace runs in fresh children for PC coverage and comparison coverage.
Their observable results must agree. WireGuard traces use network-namespace
fixtures; fixture and timing assumptions are reflected in the model's
`Leanux/Env.lean` and `Leanux/Env/`. Three QEMU slots are shared across the
checkout's worktrees by default (`LEANUX_QEMU_SLOTS`).

Run output includes validated input, the serialized guest input, observations,
coverage and hidden-input records, build and boot logs, and the QEMU command.
Malformed, missing or contradictory records fail the run. Delete the run
directory and temporary input when you no longer need them.

## Input and implementation references

- [Trace contract](../contracts/trace-v1.md): JSON envelope, descriptor
  references, FD/eventfd/pipe operations and observations.
- [`trace.py`](trace.py): validation of all operations, WireGuard fixtures,
  opcodes and guest-wire serialization. [`guest.c`](guest.c) reads that wire
  format; it is internal, so construct JSON traces rather than wire input.
- [`wg.py`](wg.py), [`noise.py`](noise.py), [`steer.py`](steer.py): netlink
  encoding, packet construction and controlled kernel inputs.
- [`linux.py`](linux.py): VM launch, record collection and failure reporting.
- [`corpus/`](../corpus/): working examples, including WireGuard scenarios.
