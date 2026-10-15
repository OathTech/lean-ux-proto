# Binary adequacy work and concrete probe

From the `task/binary-tv` worktree, with Lean v4.35.0 installed and the shared
Kraken clone/oracle at the charter's paths:

```sh
LEANUX_QEMU_SLOTS=16 capped -- /usr/bin/python3 binary/run.py
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
LEANUX_QEMU_SLOTS=16 capped -- /usr/bin/python3 binary/run.py --check .artifacts/check/<run>
LEANUX_QEMU_SLOTS=16 capped -- /usr/bin/python3 binary/run.py --trace d1_second_response
capped -- /usr/bin/python3 binary/census.py
cd binary
capped -- lake build BinaryProofs
capped -- lake env leanchecker TrustBase ServiceImage ServiceComposition KcovInvariant KcovExecution PeerCall PeerStart PeerReturn PeerFinish PeerNull PeerNullEntry PeerComparisons PeerLoad PeerDeadCallbacks PeerDeadFinish PeerDeadEntry PeerIncrement PeerLiveCallbacks PeerLiveFinish PeerIncrementFinish PeerLiveEntry FixtureKnowledge StackFrame BucketLoop Execution History HistoryRegions RegionExecution MirrorLoop MirrorPeer MirrorHistory LookupObservation Memory Image ImageLayout Layouts Regions PeerRegions PeerPrologue Prologue BucketEntry Representation KeypairRepresentation Symbolic
```

Generated state, census and comparison output go under `.tmp/binary-tv`;
guest evidence goes under `.artifacts/check`. They are disposable. Lake
dependency outputs are also private, in `../.deps/kraken/.lake` and
`../.lake`; the main checkout and other worktrees are untouched. Both packages now use Lean v4.35.0 after merging the toolchain update from
main.

The two concrete cases exercise a miss and a successful lookup with a
one-entry bucket. Peer-get executes its decoded instructions; instrumentation
and `__local_bh_enable_ip` use explicit summaries. Additional guest streams
preserve ordered coverage and comparisons in these two pinned function ranges.
Reusing an older check without those streams fails noisily.
Each case also runs the decoded service bodies with a materialized task/KCOV
fixture in PC-capture mode and checks its actual coverage buffer. It also
checks the proof-side machine observer against the logged mirror's exact
semantic decisions and call/return tags. Physical correspondence at those
points and the additional stuttering cuts is still proof work.

`binary/generate.py` regenerates the instruction regions, their layout proofs,
and DWARF scalar-field equations. All current region proofs use only Lean's
standard three axioms. The old native-reflection experiment was removed;
its results and reproduction at commit `a38e3d0` remain in the
[scoping report](../docs/2026-10-15-binary-tv-scoping.md).
No kernel memory snapshot, decoding proof or full-function simulation is
claimed. Current work and Rule Zero findings are in the
[adequacy report](../docs/2026-10-15-binary-adequacy.md).

The named draft trust surface is `TrustBase.lean`; `Pre_lookup` is deliberately
absent until its concrete satisfying witness accompanies it. The generated
service bodies are part of the same pinned decoder. To exercise their active
KCOV comparison writes and ABI/memory contracts:

```sh
capped -- binary/.lake/build/bin/binary-probe service-tests
capped -- binary/.lake/build/bin/binary-probe peer-null
capped -- binary/.lake/build/bin/binary-probe peer-nonnull
capped -- /usr/bin/python3 binary/generate.py
```

The source relation now receives the actual observed event prefix as well as
the machine state. This distinguishes two mirror decisions emitted at one
compiled edge. The relation's whole-World components and function composition
remain unfinished; the checkpoint report describes what is proved.

`KcovInvariant` proves callback readiness and preservation from physical
metadata, mapped storage and byte separation; disabled modes need no buffer.
`PeerNullEntry.null_entry_to_return` composes the helper's null-pointer path
through actual fetched instructions and the named PC callback contract.
`peer-null` executes that path with real callbacks in four configurations,
checking the complete memory and restored ABI under two undefined-value
seeds. It is a synthetic test, not a witnessed `Pre_lookup` or a kernel
entry snapshot. `PeerDeadEntry.dead_entry_to_return` and
`PeerLiveEntry.live_entry_to_return` cover the nonnull zero-count and accepted
nonzero-count paths, respectively. The live proof establishes the exact
four-byte increment. `peer-nonnull` checks both paths, including the largest
accepted count, active/disabled/full buffers and both capture modes, against
the decoded service bodies. Whole-function correspondence remains open.
