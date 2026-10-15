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
capped -- lake env leanchecker LookupLoads PeerScalars WorldParts KcovHistory PeerAccepted ServiceObservation TrustBase ServiceImage ServiceComposition KcovInvariant KcovExecution PeerCall PeerStart PeerReturn PeerFinish PeerNull PeerNullEntry PeerComparisons PeerLoad PeerDeadCallbacks PeerDeadFinish PeerDeadEntry PeerIncrement PeerLiveCallbacks PeerLiveFinish PeerIncrementFinish PeerLiveEntry FixtureKnowledge StackFrame BucketLoop Execution History HistoryRegions RegionExecution MirrorLoop MirrorPeer MirrorHistory LookupObservation Memory Image ImageLayout Layouts Regions PeerRegions PeerPrologue Prologue BucketEntry Representation KeypairRepresentation Symbolic
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

`WorldParts` is an exhaustive field decomposition, not the whole-world
relation. `PeerScalars` supplies 29 DWARF-derived stable peer equations and
physical framing; pointer/queue/work/timer components remain open.
`ServiceObservation` and `KcovHistory` retain callback histories and cuts.
`BucketShape` reads only index/type/next, with no restriction on owner peer
words. `LookupLoads` and `BucketLoop.tail_iteration` preserve the actual
intermediate instruction states needed for the pending loop composition.

`ScanNode.node_to_compare` composes the nonempty-node path +0x34 to +0x59,
including four actual instrumentation calls, with physical framing at every
appended cut. `LoopSearch.lookup_split` relates its source decomposition to
the actual logged lookup. The recursive physical loop is composed below; whole-World R remains
open. Replay these components with:

```sh
cd binary
capped -- lake build BinaryProofs binary-probe
capped -- lake env leanchecker Representation LookupLoads PeerComparisons CallHistory LookupType LoopSearch ScanFrame ScanNode
```

`ScanSearch.scan_search` executes arbitrary bucket misses to exhaustion or
the first matching index, with exact decision records/tags and physical
frames at appended cuts. It stops before the matched kind test and is not
a whole-World simulation. Replay with `capped -- lake env leanchecker
ScanFrame ScanNode ScanIteration ScanSearch` in `binary/`.

`BucketScan.bucket_loop` adds both matched type outcomes and derives the
complete source-prefix decision list. Its frames distinguish the actual
+0x9a mask boundary; `KindMask` represents every 32-bit ABI mask by its two
relevant membership tests. Whole-World correspondence remains open.
`KeypairFields.entry_peer_store` preserves the represented keypair fields
while changing its embedded peer word, including to NULL; owner-ID
correspondence is separate. Replay these additions with `capped -- lake env
leanchecker Representation LookupType ScanSearch ScanType BucketScan
KeypairRepresentation`.


The owner-shaped mirror repair is merged from `de62c9d`. `OwnerWord` and
`OwnerStore` relate and execute the single nullable peer word embedded in a
handshake or keypair; the source setter reloads the current owner. The
`dead-peer` and `dead-keypair` commands now check fixed two-lookup regressions.
They are constructed states, not kernel entry snapshots.

`DeviceScalars`, `SerialCpu` and `ListRing` add exact stable fields and active
circular-list components for whole-World R. Names, object-store membership,
retirement, and the remaining heap components are separate obligations.
`PeerPrologueHistory`, `PeerSignHistory`, `PeerReturnHistory`,
`PeerSavedHistory` and `PeerFinishHistory` retain actual helper instruction
histories; `MirrorPeerPoints` identifies the corresponding source worlds.
The complete helper and lookup correspondence proofs remain open.

Replay the current owner, list and helper-history components in `binary/`:

```sh
capped -- lake env leanchecker Layouts SerialCpu DeviceScalars ListRing MirrorLoop MirrorHistory MirrorPeerPoints LoopSearch PeerSignHistory PeerReturnHistory PeerSavedHistory PeerPrologueHistory PeerFinishHistory OwnerWord OwnerStore BucketScan
```


`PeerNullEntryHistory.null_entry_history` now composes the complete physical
null-helper path, including both actual callbacks and RET, with exact
observer events and memory framing at every appended cut. It does not yet
supply whole-World R or the nonnull helper paths. Replay with `capped -- lake
env leanchecker PeerClearHistory PeerStartHistory PeerNullHistory
PeerNullEntryHistory`; `binary-probe peer-null` exercises the actual service
bodies under two undefined-value seeds.


`PeerDeadEntryHistory.dead_entry_history` now composes the actual mapped
zero-count helper path from entry through RET, all five decision states,
and per-cut memory framing. `PeerNonNullPrefixHistory` obtains the count
from the physical word and admits zero. These components do not yet supply
the complete helper's whole-World relation. Replay the nine modules named
in the dead-helper report; `binary-probe peer-nonnull` exercises 21 cases
with actual service bodies and two undefined-value seeds.


`PeerIncrementFinishHistory.increment_finish_history` composes the actual
live increment through RET and exports the post-increment memory frame at
every later decision and cut. `PeerLiveZeroHistory` supplies the preceding
nonzero guard/callback. The full live entry and whole-World correspondence
remain open. To replay imports as well, run one module per invocation:
`capped -- lake env leanchecker --fresh PeerLiveZeroHistory` and
`capped -- lake env leanchecker --fresh PeerDeadEntryHistory` in `binary/`.


`PeerLiveEntryHistory.live_entry_history` now composes the accepted live
helper entry through RET, retaining all six decision states and the exact
physical increment. Null/zero cuts frame entry memory; later cuts frame
the incremented memory. Together with null/dead histories this covers all
accepted physical helper paths. The whole-World accepted helper theorem
and lookup adequacy remain open. Replay imports with one root:
`capped -- lake env leanchecker --fresh PeerLiveEntryHistory` in `binary/`.


`IndexHeap` now supplies exact hlist forward/backward links, all-bucket
framing and projection to `BucketShape`. Its mutation fold still needs actual
incoming provenance and owner/lifetime naming. `EndpointHeap` decodes active
endpoint fields with exact byte order and leaves inactive union bytes alone.
`WorldContext` derives decision logs from observed events under one fixed
nonphysical context; its event cursor handles compiler-merged decisions.
These remain components of the unfinished whole-World R.
