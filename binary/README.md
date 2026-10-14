# Binary-level translation-validation probe

From the `task/binary-tv` worktree, with Lean v4.35.0 installed and the shared
Kraken clone/oracle at the charter's paths:

```sh
capped -- python3 binary/run.py
```

This verifies a private source archive against Kraken commit `8af7806`, builds
the probe, runs the existing differential checker on
`d1_wrong_receiver_index_same_bucket`, replays the mirror prefix, extracts
DWARF layouts, runs the index lookup's machine instructions and compares
return/memory, coverage PCs, operands and decisions. Unknown paths and
mismatches fail. Binutils, system Python with pyelftools, the project bundle
and a locally installed Lean toolchain are required; nothing is downloaded.

The default command makes a new recorded run. To reuse a completed one:

```sh
capped -- python3 binary/run.py --check .artifacts/check/<run>
capped -- python3 binary/census.py
cd binary
capped -- lake env lean Symbolic.lean
capped -- lake env lean Axioms.lean
```

Generated state, census and comparison output go under `.tmp/binary-tv`;
guest evidence goes under `.artifacts/check`. They are disposable. Lake
dependency outputs are also private, in `../.deps/kraken/.lake` and
`../.lake`; the main checkout and other worktrees are untouched. Root
v4.33.1 builds and this v4.35.0 experiment must not run concurrently in this
worktree's shared mirror build directory.

This is one recorded **miss** with a one-entry collision chain. Instrument
calls and `__local_bh_enable_ip` have explicit summaries; a reached peer-get
call rejects. Kernel PCs are deduplicated, so their equality here does not
establish arbitrary loop multiplicity. No kernel memory snapshot, decoding
proof or full-function simulation is claimed. See the
[report](../docs/2026-10-15-binary-tv-scoping.md) for the state relation,
assumptions, complete census and eight charter answers.
