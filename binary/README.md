# Binary adequacy work and concrete probe

From the `task/binary-tv` worktree, with Lean v4.35.0 installed and the shared
Kraken clone/oracle at the charter's paths:

```sh
capped -- python3 binary/run.py
```

This verifies the private Kraken branch against the dependency lock, builds
the probe, runs the existing differential checker on
`d1_wrong_receiver_index_same_bucket`, replays the mirror prefix, extracts
DWARF layouts, runs the index lookup's machine instructions and compares
return/memory, coverage PCs, operands and decisions. Unknown paths and
mismatches fail. Binutils, system Python with pyelftools, the project bundle
and a locally installed Lean toolchain are required; nothing is downloaded.

The default command makes a new recorded run. To reuse a completed one:

```sh
capped -- python3 binary/run.py --check .artifacts/check/<run>
capped -- python3 binary/run.py --trace d1_second_response
capped -- python3 binary/census.py
cd binary
capped -- lake build BinaryProofs
capped -- lake env leanchecker Execution RegionExecution MirrorLoop Memory Image ImageLayout Layouts Regions PeerRegions Prologue BucketEntry Representation Symbolic
```

Generated state, census and comparison output go under `.tmp/binary-tv`;
guest evidence goes under `.artifacts/check`. They are disposable. Lake
dependency outputs are also private, in `../.deps/kraken/.lake` and
`../.lake`; the main checkout and other worktrees are untouched. Root
v4.33.1 builds and this v4.35.0 experiment must not run concurrently in this
worktree's shared mirror build directory.

The two concrete cases exercise a miss and a successful lookup with a
one-entry bucket. Peer-get executes its decoded instructions; instrumentation
and `__local_bh_enable_ip` use explicit summaries. Additional guest streams
preserve ordered coverage and comparisons in these two pinned function ranges.
Reusing an older check without those streams fails noisily.
Each case also runs the decoded service bodies with a materialized task/KCOV
fixture in PC-capture mode and checks its actual coverage buffer.

`binary/generate.py` regenerates the instruction regions, their layout proofs,
and DWARF scalar-field equations. All current region proofs use only Lean's
standard three axioms. The old native-reflection experiment was removed;
its results and reproduction at commit `a38e3d0` remain in the
[scoping report](../docs/2026-10-15-binary-tv-scoping.md).
No kernel memory snapshot, decoding proof or full-function simulation is
claimed. Current work and Rule Zero findings are in the
[adequacy report](../docs/2026-10-15-binary-adequacy.md).
