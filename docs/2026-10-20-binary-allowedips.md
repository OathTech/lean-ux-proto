# Allowed-IPs binary refinement: scaling report

Status: work in progress on `task/binary-allowedips`, based on landed main
`1f766662` after the authorized rebase (original base `1a69cebb`). Neither
checkpoint A nor B is complete. The
[charter](2026-10-20-charter-binary-allowedips.md) defines the target; the
[independent review](2026-10-20-review-binary-allowedips-charter.md) records its
three findings. Work began at 2026-10-20 01:25:17 UTC, including preparation.

## First Rule Zero finding: the allowed-IPs sequence counter

At discovery, the mirror's `AllowedIps.seq` was a Nat and insertion
incremented it without truncation. Linux stores a u64, and the compiled wrappers increment that word.
This is observable state: the dump tests a saved counter against zero and the
current sequence. It cannot silently be reclassified as an unobserved epoch.

The constructed-state reproducer executes both compiled insertion wrappers,
the invalid-prefix path of `add.isra.0`, and the actual coverage/comparison
bodies, to the original ABI return. It supplies a mapped peer and empty list,
an empty table, network-order address storage, stack and coverage resources.
There are no allocator substitutions or calls on this path. This is not a
captured kernel entry or a theorem of entry reachability.

| Entry sequence | Families / CIDRs | Binary result / sequence | Mirror result / sequence |
| --- | --- | --- | --- |
| 1 | IPv4 / 33, IPv6 / 129 | `-EINVAL`, 2 | `-EINVAL`, 2 |
| 2^64 - 1 | IPv4 / 33, IPv6 / 129 | `-EINVAL`, 0 | `-EINVAL`, 2^64 |

Both undefined-value seeds (0 and all ones) produce these results. IPv4 executes
124 instructions and IPv6 127, including the real service bodies. The runner
checks the return PC/stack and callee-save registers. The permanent reproducer
failed with exit 1 for that mismatch before the fix; the historical result
is not a passing refinement test:

```sh
capped python3 -B binary/allowedips_seq_wrap.py
```

The script verifies the s5 image and clean private Kraken pin, extracts actual
instructions and DWARF offsets, builds `binary-allowedips-seq-wrap`, and runs it.
Its disposable input is `.tmp/allowedips/seq-wrap.json`. After a mirror fix the
same comparator should pass without changing its expected binary result.

F1 was assigned to the coordinator's mirror lane [USER 2026-10-20]. The
correction is now on main at `1f766662`, and the preserved witness passes as
reported in the carry checkpoint below. No non-wrapping precondition or
modulo target was introduced. The charter retains exact counter correspondence.

## Review dispositions and preparation

F2 is addressed in the charter with separate live, retired and released
resources; pending forest child pointers survive logical erasure, the
`peer_list`/`rcu` union changes ownership, and only actual release permits reuse.
An explicit serialized event schedule dispatches the actual WireGuard callback
bodies. This design still needs implementation and proof.

F3 is addressed with an operation-specific ABI inventory, explicit accepted-run
limits for dying-peer retries, and a required frame lift from the old lookup
projection to table roots/counter, parent links and ownership lists. That lift
is part of checkpoint A, not an assumption about its successor.

The s5 inventory finds 506 instructions in `add.isra.0`, 26/29 in the insertion
wrappers, 120 in removal-by-peer, 37 in free, 80 in readout and 57 in each lookup
wrapper. The WireGuard-owned `root_remove_peer_lists`, `node_free_rcu` and
`root_free_rcu` bodies have 71, 7 and 58 instructions. These counts describe
work, not completed proof coverage. Register-form BT is an ISA gap on two
insertion paths, to be addressed privately with tests.

Baseline setup and validation pass: private pinned Kraken bootstrap, the
283-job paired-trie/callback executable build, the 130-job model build, and
136 fast-tier unit tests (one skip). No new headline theorem is claimed yet.
The counter mismatch was confirmed during the first ten minutes of work.

Development failures so far: an initial read targeted the already-removed
landing worktree; several guessed source paths did not exist; the first witness
draft missed required World fields and used an invalid Int64 conversion name;
one correction used the wrong working directory; the first binary input omitted
the shared `write_comp_data` tail and correctly failed on its missing PC.
These were repaired before the reported executions. The counter mismatch
remains a semantic failure. No KILLED banner, timeout or sandbox denial occurred.

## Register BT extension

The private Kraken branch now implements the register/register BT forms used by
insertion, at `907830a1fb207e86f7914764717e3995c1f0df2d`, reproducible as patch
0009. Register offsets wrap at the operand width; CF receives the selected bit,
ZF is preserved, and OF/SF/AF/PF are undefined, following
[Intel SDM volume 2A, BT](https://cdrdv2-public.intel.com/812383/253666-sdm-vol-2a.pdf).
Neither operand register changes, including the upper half on a 32-bit operand.
Unsupported 8-bit, memory, immediate and LOCK forms fail closed.

Focused Lean tests cover widths, boundary/wrapped offsets, aliases, register
preservation and all undefined flag choices; parser/printer roundtrips pass.
The native hardware comparison `test_bt.S` passes (1/1). Reproduce in the private
Kraken checkout with the consumer toolchain selected:

```sh
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 capped lake build Kraken.X64.BtTests Kraken.X64.PrintATTTests krakenrunner_x64 att2intel
capped python3 Kraken/X64/Test/asm_tests.py Kraken/X64/Test/asm/test_bt.S
```

Test development exposed incomplete flag fixtures and missing execution-access
handling in the test traversal, then a missing meta printer import. The ATT
corpus test requires Kraken as its working directory. The native runner also
needed a Bool generator for previously added instruction fields; that test-only
repair is in the patch. These failed builds were repaired before the reported
passes. The full consumer proof rebuild remains due under this new pin.

## First retained-heap execution checkpoint

At roughly 27 minutes from the start, the paired mutation runner passes four
constructed sequences: IPv4 and IPv6, each with undefined-value seeds zero and
all ones. There are 54 insertion calls and 54 subsequent lookup calls. The
measured executable time is 2.573 seconds, excluding extraction and build.
This is runtime progress; neither A nor B has a function-level proof yet.

The cases cover invalid prefixes, empty-root allocation and failure, exact
reassignment, both child slots, covering roots, intermediate roots and children,
all three allocation failure sites, rollback and reuse of the released address.
IPv6 also exercises differing low words. Full reconstruction at every return
checks roots/counter, nodes/packed parents, ordered peer lists, peer counts and
the ghost allocation counter. Lookup runs against the same physical heap.

Generic allocator/free bodies are supplied interface returns, clearly labelled;
they are not claimed as executed. The WireGuard and coverage/comparison bodies
are interpreted. Successful allocation supplies zeroed fresh bytes and advances
the identity counter; rollback free removes the owned bytes and only then makes
the address reusable. Source allocation records use their real 40-byte shape
and site IDs. These are generated cases, not captured entry states.

The runner checks ABI result, stack/callee-save restoration, unchanged preempt
and pending words, and exact stored coverage prefix. Coverage accounting uses
the executable KCOV plan, including the buffer-full path. The initial test
version counted every callback encounter in its diagnostic list; that was
corrected before the measured rerun above. No later call rematerializes the
WireGuard heap. Reproduce:

```sh
capped python3 -B binary/allowedips_mutation.py
```

All 561 insertion instructions now have literal decoded layouts, across 137
small chunks, proved with standard axioms through the extended instruction
monotonicity lemma. These are layout witnesses, not simulated mutation regions.
The initial long-region layout proof exhausted default recursion depth.
Balanced region fetch and chunks of at most eight instructions close it at the
default limits; the checked instruction sequence is unchanged. Regenerate with:

```sh
capped python3 -B binary/generate_allowedips_mutation.py --check
capped lake -d binary build AllowedipsMutationCodeLayout PairAllowedipsState
```

Fast tier passes: 136 unit tests, one skip. The independent s5 recording for
`b1_trie_routing` uses the new `allowedips-insert` coverage profile.
Profile ranges come from ELF symbols,
with source attribution for local symbols; no guest or kernel change is needed.
Additional development failures were record-layout indentation, an image/layout
output-name collision, ambiguous local `lookup` extraction, and a check output
path outside the checker's required `.artifacts` tree. These were corrected.

## Recorded comparison and actual-entry capture

The full differential recording passes: one trace, 12 operations, 396 compared
pairs, 244 distinct pairs. The paired insertion comparison then passes eight
mixed-family calls under both undefined-value seeds: 170 stored coverage points,
64 comparison records and 117 mirror decisions, in 0.214 seconds of execution.
The initial comparison failed because allocator records were not armed; the
profile now arms the three existing allocation sites without steering them.
Another corrected assumption was that all 39 bytes after the allocation outcome
were zero: actual records carry unwind metadata, which the source does not use.
These calls retain the physical heap, but their entry is constructed from the
recorded arguments and outcomes, not a captured kernel entry.

The first IPv4 insertion also has an actual stopped-QEMU entry, allocator
boundary and ABI-return capture. It records 254 WireGuard/coverage instructions
and 8,274 native steps including the generic allocator, in 35.732 seconds.
The capture carries 33,558,136 actual entry bytes, including the complete KCOV
allocation. The allocator body is executed by QEMU and supplied as an external
transition in Kraken; it is not interpreted or proved here. Its replay validates
arguments, fresh zeroed allocation, ABI restoration and the protected bytes;
only its declared stack, coverage and new allocation bytes may change.

Kraken replay passes for both undefined-value seeds, comparing every general
register, represented status/system flags, the interpreted instruction sequence,
and 822,856 captured bytes at return. The shared full reconstruction is checked
at entry and return. Loading the actual memory and both replays take 79.124
seconds. This is a concrete witness and an independent endpoint comparison,
not a universal refinement theorem or a caller-reachability proof.

The first replay correctly failed on the source fixture's peer count: the
captured count is two, because `setPeerCmd` takes a temporary reference after
creation. The repaired setup executes the mirror's `peerGet` from a freshly
created peer; it does not copy the captured count into the source. The assertion
is unchanged. Public-key identity and the query are checked independently by the
capturer. Placeholder cryptographic fields are outside this projection.

Reproduction commands, including recording and capture, are in
[binary/README.md](../binary/README.md#allowed-ips-mutation-scaling).
The three-way check fails if outcomes are absent or any coverage, comparison or
decision sequence differs. No guest or kernel edit was needed. Capture launch
failures exposed bundle Python's absent pyelftools and host PATH's absent QEMU;
host Python now drives the bundled QEMU when necessary. The first capture Lean
build also failed on an ambiguous type name and record syntax before correction.
No capture snapshot is committed; these files are reconstructible in `.tmp`.

## Proof work and measured friction

`PairAllowedipsFrame` proves that the exact executable reconstruction survives
an arbitrary write footprint disjoint from its reads. Its peer-list traversal
checks that a link is an owned node or the head before reading through it.
`AllowedipsCounterRegion` proves the actual u64 increment and write frame at
both wrapper locations, for every old word including the wrapping case.
Both modules report only `propext`, `Quot.sound` and `Classical.choice`.
They are supporting lemmas; no insertion function is counted as proved.

One frame-proof attempt spent 70 seconds in reduction after the decoder's
monadic `unless` expanded a large continuation. I terminated that specific
Lean process; exit 143 is a failed build. Rewriting the same fail-closed link
test as an explicit outer conditional made the proof check in about one second
at the default limits. This changed the binary-side decoder's expression shape,
not the mirror or the accepted heap invariant. It is a concrete instance where
small executable-definition choices affect proof cost substantially.

The lookup composition obligation now checks. `Allowedips.lookup_checked` in
`PairAllowedipsLookupAdequacy` lifts the existing complete lookup theorem to the
extended executable assertion, including table roots and sequence, packed
parents, ordered ownership lists, peer counts and the heap invariant. Its
entry check derives the root from the source table related to the bytes and
checks separation of metadata from the actual lookup write footprint. The
existing physical theorem and its frame establish the extended postcondition;
no new instruction proof or assumed post-correspondence is introduced. The
retained-heap runner now executes this stronger boundary check on every lookup.
This strengthens an existing function result and adds no completed-function
coverage. The same accepted-source-run restriction and explicit callback and
decoder hypotheses remain.

The new support and headline occupy approximately 570 lines. From the captured
replay checkpoint at 02:12:37 UTC to the successful lookup build at 02:25:24 UTC
was about thirteen elapsed minutes, including other work; this is composition
cost, not a new-function throughput measurement. A fresh full-closure kernel
replay of `PairAllowedipsLookupAdequacy` passes, and the headline prints only the
three standard axioms. External export acceptance of this new surface remains
pending.

`PairAllowedipsPlacement` exposes the mirror's actual placement iteration as an
executable accumulator and checks its binary locals and full reconstruction at
the loop header and both exits. `Placement.run_eq_source` proves that this
exposed loop is the mirror's `nodePlacement`. The first assertion run failed:
a saved stack word was incorrectly identified as the requested prefix rather
than the address width. Correcting that binary-local assertion gives 82 checked
loop-header visits across 54 generated insertions and 54 retained-heap lookups
in about 2.2 seconds. The eight-call recorded three-way comparison also passes
under both seeds, in 0.227 seconds. These are tested invariant candidates and a
source-identity lemma; the physical placement-loop proof is still open.

Reproduce the new proof checks with:

```sh
capped lake -d binary build PairAllowedipsLookupAdequacy PairAllowedipsPlacementSource
capped lake -d binary env leanchecker --fresh PairAllowedipsLookupAdequacy
```

Insertion's placement loop and mutation regions, then its function theorem,
remain open. F1 is independently confirmed; the coordinator's `task/seq-wrap`
correction is pending its claim point and landing notice. The failing witness,
exact target and unrestricted wrapping case remain unchanged on this branch.

## Reused helper and placement segments (03:00 UTC)

Both insertion call sites now use `Allowedips.common_checked`: the actual CALL,
all `common_bits` instructions and RET, the source arithmetic result, restored
ABI, coverage invariant and scratch frame. The old physical instruction and
arithmetic proofs are reused. Their history wrapper fixed lookup's return PC;
the new sequential wrapper generalizes that caller datum and omits internal
decision histories. The original lookup caller remains supported by the default
return parameter. The runner executes the same `Common.callerCheck` assertion
at the placement call site.

The placement comparison regions, argument preparation, child selection and
its actual saved-parent write check. A shared frame carries callback readiness,
six readable scratch words, fixed input registers and the combined scratch,
parent-slot and coverage write footprint. `Frame.common_segment` joins argument
preparation with the complete helper from entry-memory premises. Separately,
`Placement.compose_loop` composes the actual source loop given its iteration
simulation; that iteration premise is still open, so this is not a loop proof.

This checkpoint adds 1,069 lines across helper reuse, executable checks,
physical segments and composition support. From the previous lookup build at
02:25:24 to this checkpoint is about 35 elapsed minutes, including validation
and rebuilds. There is no new completed insertion function. The useful reuse
so far is the helper's instruction proofs and one shared physical frame; it
does not yet establish viable whole-function cost.

With all new runtime separation assertions, the generated retained-heap suite
passes 54 insertions and 54 lookups in 2.203 seconds. The recorded eight-call,
two-seed three-way comparison passes in 0.271 seconds with the same 170 coverage
points, 64 comparisons and 117 decisions. Local Lean builds pass with standard
axioms; fresh replay of the new helper/segment closure passes, and external
export acceptance remains pending. A first trust-surface print failed because
this fresh worktree had not built the old headline roots; building those roots
resolved it. No failed print was treated as acceptance.

The surface now prints the stronger lookup, shared helper and their tested
definitions. Its only added environmental declaration is
`AllowedipsMutationDecoderAgreement`, agreement with the literal ELF-derived
instruction terms for the two insertion wrappers and `add`. It contains no
execution or desired postcondition premise. The existing explicit coverage
callback contracts are retained. Full insertion's allocator contracts and
function postcondition are still to be implemented and proved.

## Placement-loop composition (03:17 UTC)

`Placement.loop` now proves the complete physical placement loop against the
actual accepted `WG.nodePlacement` run. It uses the shared `compose_loop` and
`Sequential.forIn_execution` lemmas, with a proved physical iteration. Its
invariant includes the full executable reconstruction and heap assertion; these
are reestablished by the physical frame, without assuming future correspondence.
The source component store is unchanged. The endpoint exports the selected
parent, exact/nonexact exit PC, callback readiness, scratch/parent write frame,
and the restored width and peer registers on nonexact exits.

This is still a loop-boundary result under explicit entry-byte `Inputs`, not
an insertion function result. Deriving those read facts from the runner's
executable boundary is the next obligation, followed by mutation and wrapper
composition. The conditional hypotheses are named decoder and coverage
callback contracts; no binary step or postcondition is assumed. The original
source body supplies its accumulator result and unchanged store through
`iteration_accepted`, with source records remaining in Ambient.

Composition exposed two missing facts in the initial support. Callback/helper
contracts discarded preservation of the saved-parent word; they now export it
from their smaller proved write footprints. The generic loop lemma initially
asked for an iteration proof even for an already-completed accumulator; it now
uses an explicit continuing-accumulator predicate, proved for every yielded
source step. These were proof-interface defects, not changes to the mirror or
to the counter abstraction. Reachability restricts node input facts to the
selected family/path, so a mixed-family heap is not required to give every
node the current call's width.

The new source projection, physical composition and loop files add about 770
lines, plus small changes to the shared frame and loop lemmas. From the 03:00
support checkpoint to the successful loop build at approximately 03:17 is about
17 elapsed minutes. Generated executions pass with added query/saved-input
separation assertions: 54 insertions and 54 lookups in 2.225 seconds. The
eight-call recorded comparison passes under both seeds in 0.269 seconds.
All new declarations build with the standard axioms. Fresh kernel replay of
`AllowedipsPlacementSimulation` passed; external acceptance is pending.
The test counts and loop result add no completed-function coverage.


## Checked placement boundary (03:34 UTC)

`Placement.loop_checked` derives every placement-loop input and its initial
invariant from the same executable `Placement.header` used by the runner.
It then applies the complete loop proof. Reconstruction, structural heap,
query bytes, saved inputs, callback readiness and separation are checked at
entry; the theorem does not take a physical iteration or future relation as
an assumption. It supports both families and every accepted placement exit,
including internal-node traversal. Its boundary is the nonempty placement
header, not the public insertion entry. Mutation and wrapper composition remain
open, and there is no new completed-function coverage.

The bridge adds 350 proof/support lines and factors the executable assertion
into cursor, saved-input and family-specific query checks. From the earlier
loop checkpoint at 03:17 to this checkpoint is about 17 elapsed minutes,
including failed proof reductions and validation. Generated executions pass
54 insertions and 54 retained-heap lookups in 2.248 seconds. The recorded
three-way comparison passes eight calls under both seeds in 0.281 seconds,
with 170 coverage points, 64 comparisons and 117 decisions. The printed surface
now includes `loop_checked`, its entry assertion, frame and read/write covers;
no environmental premise was added to `TrustBase.lean`. The new full-closure
fresh replay passed; external acceptance remains pending.

Proof-development failures were real failures. Several large assertion-decoding
attempts were stopped after excessive growth; one accidental overlap of two
writer builds was detected and both owned processes were stopped. Other
attempts failed kernel checking after about 80 seconds with a deep-recursion
error. A profiled diagnostic localized the latter to the combined query proof:
elaboration took about 0.07 seconds while kernel checking took about 77 seconds.
Splitting the executable IPv4 and IPv6 checks and their lemmas eliminated that
reduction, with the complete local-check proof module checking in under a
second. The small `require` guard also separates a failing assertion from its
continuation and has a proved equivalence to the prior `unless` idiom. No limit
was raised, failure counted as a pass, or proof bypass introduced. This is a
concrete example where executable/proof decomposition reduced tooling cost;
it does not measure full mutation-proof cost.

The coordinator's counter correction is still pending a landing notice. The
wrap witness and its expected binary zero are unchanged. Neither this entry
assertion nor reconstruction excludes wrapping sequence states or substitutes
a modulo target. The mirror and main remain untouched.


## Exact-reassignment effect and list support (03:47 UTC)

The 14-instruction callback-free reassignment segment now proves the same
`Exact.effect` memory/register summary that the paired runner checks at its
actual entry and exit cuts. The proof covers all mapped read/write cases; it
does not assume a resulting list relation. The destination tail is read after
unlinking, preserving same-peer moves, including a singleton, a move to the
tail, an already-last node and an internal self-linked node acquiring a peer.
The full-memory comparison includes unchanged bytes. The runner checks that
the number of executed segments matches the source's exact-update branch count.

Generated runs now pass 66 insertions and 66 retained-heap lookups in 2.574
seconds, including 20 checked exact segments. The recorded three-way comparison
still passes eight mixed-family calls under both seeds in 0.273 seconds, with
the same coverage/comparison/decision counts. Generic allocator/free returns
remain supplied. The source counter correction remains pending and the wrap
witness remains a failure on this mirror pin.

For reconstruction after writes, a finite circular-list presentation is proved
necessary and sufficient for the existing executable list decoder, including
fuel and cycle checks. Structural unlink and append lemmas retain the sentinel
backlink and recover decoding after local word effects. Identity filtering is
proved to equal source node-ID filtering. These adapt the earlier index-chain
proof pattern. A small ordered-word-write lemma is used by both the actual
unlink/owner stores and append stores; equal destinations are resolved in
instruction order, while distinct word ranges require byte separation.
Allocation geometry is derived from existing reconstruction validation,
without imposing new base-alignment or relation clauses.

This checkpoint adds 844 lines for the executable effect, physical proof and
reconstruction support, approximately 14 minutes after the checked-loop
checkpoint. The physical effect is complete; connecting its word equations to
full reconstruction and the mirror's exact-update effect remains open. It is
not an exact-path insertion theorem or completed-function coverage. All modules
build with standard axioms. The first fresh-replay invocation incorrectly gave
multiple roots with `--fresh` and failed; the corrected invocation uses the
single partial-work root `AllowedipsInsertionSurface` and passed. No
external export acceptance is claimed. The complete insertion, allocation and
rollback proofs, wrapper composition, and checkpoint B remain open.

## Reassignment destination reconstruction (03:58 UTC)

`Exact.segment_destination` connects the actual 14-instruction segment to the
existing executable destination-list decoder. The resulting identity sequence
is the old list with the focus removed and then appended. It covers same-peer
singleton, move-to-tail and already-last updates, and an internal self-linked
node joining a peer. The post-unlink tail read supplies its own named slot;
the traversal budget follows from the existing finite interpretation. There
is no new fuel, alignment, no-alias or no-wrap precondition. Local input facts
about the focus and its neighbors still need to be derived from full entry
reconstruction and the heap assertion in the function composition.

The supporting unlink theorem also reconstructs deletion in every peer list,
including lists that did not contain the focus. The append theorem and the
physical-effect equality preserve the actual store order. Allocation geometry
separates forward, backward and owner fields without assuming peer-base
alignment. These lemmas will also serve insertion and deletion; no generic
search tactic was introduced. All new modules build with standard axioms and
no resource-limit increase. A fresh replay of the enlarged partial-work root
passed at `5d7678ba`. The previous root's replay passed at `f922daa4`.

This adds 731 proof/support lines approximately eleven minutes beyond the physical-effect checkpoint. The fast unit tier passes 136 tests (one skipped) in 23.036 seconds; its printed empty-report failure is the expected unit-test fixture, not a differential run.
It is still a partial postcondition: owner-word reconstruction, the other peer
lists and unchanged fields, the source-state update, and wrapper composition
remain to be assembled. It adds no completed-function coverage. The mirror
counter finding remains open pending the coordinator's landing notice; the
failing witness and binary result are unchanged.

## Full reassignment reconstruction and source fragment (04:22 UTC)

`Exact.assignment_simulation` now connects the same tested 14-instruction
segment to the actual mirror operations `setNode`, `listDel` and
`listAddTail`, reestablishing the complete allowed-IPs reconstruction. It
updates the owner word and every ordered peer list, and preserves the roots,
sequence, prefixes, keys, children, packed parents, peer counts and allocation
counter. This is a segment theorem: public entry-to-return composition and
preservation of the structural heap assertion remain open. It adds no
completed-function coverage.

The local focus, neighbor, list-disjointness and traversal facts now follow
from entry reconstruction and its existing heap assertion. They are not new
restrictions on admissible aliases or ownership states. The memory proof
preserves actual store order, including reading the destination tail after
unlink. The source bridge reuses the landed mirror's list-operation lemmas
and exact-device update. No mirror code or environmental assumption changed.

The full reconstruction/source bridge adds 1,216 lines across fifteen small
modules, about 24 elapsed minutes beyond the destination-list checkpoint,
including proof failures and validation. The initial source bridge failed
Lean elaboration; the failed output included the resulting `sorryAx` and was
not accepted. After repair, its explicit axiom print contains only `propext`,
`Classical.choice` and `Quot.sound`, and fresh kernel replay of the enlarged
`AllowedipsInsertionSurface` closure passes. The default binary package build
passes. The fast unit tier passes 136 tests, one skipped, in 25.057 seconds.
The expected trust surface now prints the segment statement and executable
effect definitions. No external export acceptance is claimed.

Two additional support lemmas build for the next obligation: the trie
structural check ignores peer-word changes, and the full executable heap
check decomposes into its structural and ownership checks. These preserve
the tested definitions by proved equalities; no runtime checker was replaced.
Post-mutation heap preservation, allocation/failure/rollback paths, wrapper
composition and checkpoint B remain work to do. The counter correction is
still awaiting its landing notice; the wrap witness and its expected binary
result remain unchanged.

## Reassignment closed at the tested segment; empty-root work (04:43 UTC)

`Exact.assignment_from_relation` now derives successful execution of the tested
memory effect from entry reconstruction and the existing heap assertion. Its
14-instruction segment executes the actual mirror assignment fragment, exports
an exact byte write frame and restores both full reconstruction and the tested
heap invariant. Successful future execution, a successful effect computation,
post-mutation correspondence and extra separation premises are not assumptions
of this segment headline. Public entry/return and the other insertion paths
remain open; this adds no completed function.

The heap proof reuses the existing ownership and structural checks. Unlink and
append preserve the self-linked lists of other internal nodes; distinctness of
those nodes from the actual predecessor, successor and post-unlink tail follows
from decoded words and ownership. Mapped writes are derived from those reads.
The strengthened root has only the three standard axioms and passes fresh kernel
replay. The printed trust-surface diff passes. No new environmental premise was
added to `TrustBase.lean`, and no external acceptance is claimed.

For empty-root insertion, the runner now checks an executable whole-memory
summary from `add+0x443` to `add+0x549`. It follows actual read/store order,
including the compiler's duplicate IPv4 copy and the saved root-slot read after
the key copy. The first two physical blocks (sixteen instructions) and the
packed-header arithmetic build with standard axioms, without raised resource
limits. The finite header facts use kernel reduction, not native reduction.
The copy, root connection and reconstruction composition remain open.

Generated checks pass 66 insertions followed by 66 retained-heap lookups, plus
24 separately labeled fresh-fixture root-prefix cases with immediate retained
lookups (both families, both seeds, prefixes 0, 1, 7, 8, width-1 and width).
They check 20 exact segments and 28 root segments, in 3.403 seconds. The recorded
three-way run passes eight mixed-family calls under both seeds: 170 coverage
entries, 64 comparison entries and 117 decisions, in 0.275 seconds. These
recorded arguments still use constructed entry state. The actual captured first
insertion also replays successfully under both seeds with the new root check:
254 interpreted WireGuard/coverage instructions and 822,856 endpoint bytes per
run. Its captured generic allocator transition remains supplied, not proved.
The fast unit tier passes 136 tests, one skipped, in 24.786 seconds.

This checkpoint is about 21 elapsed minutes after the source-fragment bridge.
The eight new modules add 600 lines; the strongest reassignment segment uses
the existing checked definitions. Proof elaboration failures in the new register arithmetic were repaired before
acceptance; their intermediate `sorryAx` output was a failed build. The mirror
counter correction remains unlanded, and the existing failing wrap witness and
binary expected result are unchanged. Allocation, rollback, wrappers and
checkpoint B remain open.

## Complete empty-root tail effect (05:14 UTC)

`Root.effect_segment` now realizes the same executable whole-memory effect
checked by the paired runner, from `add+0x443` after allocation return to
`add+0x549` after publication. It covers both address families: 47 instructions
on the IPv4 path and 53 on IPv6, 60 distinct instructions in their union.
Sixteen had physical proofs at the preceding checkpoint. The result includes
exact final memory, the zero success register, the unchanged stack and saved
registers, and the updated peer-list-head register. No allocator behavior,
post-state correspondence or byte-separation contract is assumed by this local
effect proof. Its premise is successful evaluation of the executable entry
summary; deriving that from fresh-allocation resources and reconstructing the
new mirror node remain open. This is not an insertion-function theorem.

The summary is factored into attachment, copy and publication phases with the
same read/write order. The proof uses these tested definitions and composes
physical regions at proof-selected cuts. The root-slot load still follows the
key copies, and the duplicate IPv4 copy still reads the first store's memory.
There is no intermediate full-world correspondence requirement. Existing
region composition and memory lemmas suffice; no new search tactic was added.

An allocation-name helper is now shared with the supplied-service runner.
Its body is the previous record update unchanged. Supporting lemmas preserve
already resolved pointers and decoded peer lists when one identity is appended;
the list budget increases with that same interpretation. Resolving the new
pointer requires physical-address freshness. Validation of the extended
allocation geometry and reconstruction of the newly initialized node remain
separate obligations. These support lemmas build with standard axioms; the fresh
replay below covers the insertion surface, not a completed allocation theorem.

This checkpoint adds 828 lines in nine root-proof modules and two allocation-name
modules, about 31 elapsed minutes beyond `fe591115`. That includes diagnosis,
failed attempts and validation. The complete physical tail composes in 83 lines;
this is a local composition cost, not a forecast for structural insertion or the
campaign.

Two proof-engineering costs were exposed. Expanding header arithmetic through
memory cases made an initial symbolic block excessive; separating pure register
arithmetic from the store avoids that expansion. Separately, assigning
`Nat.mod_eq_of_lt` directly to a bit-vector-to-Nat equality caused expensive
definitional conversion. An isolated reproducer located that step; explicitly
rewriting with `BitVec.toNat_ofNat` makes the composed module elaborate in about
a second. No statement, precondition or resource limit was weakened. Eight
oversized build/probe attempts were intentionally terminated (failures), and
one diagnostic capped at 8 GiB was KILLED with exit 137 (also a failure).
One leaf build was inadvertently started while another was still running;
subsequent serialized package validation passed. Ordinary elaboration errors
were fixed before acceptance, with no remaining `sorryAx` in the headlines.

Validation:

- The default binary package build passes without warnings. Explicit axiom
  prints for `Root.effect_segment`, `Exact.assignment_from_relation` and the
  allocation-name lemmas contain only `propext`, `Classical.choice`, `Quot.sound`.
- Fresh `capped lake -d binary env leanchecker --fresh
  AllowedipsInsertionSurface` passes for the enlarged root-effect closure.
  The expected printed statement/definition surface was reviewed and updated;
  its diff check passes. `TrustBase.lean` is unchanged. External export
  acceptance remains unclaimed.
- Generated checks after the shared name-update refactoring pass 66 insertions
  and 66 retained-heap lookups, plus 24 isolated root insertions/lookups, checking
  20 exact and 28 root segments in 3.348 seconds.
- After phase factoring, the recorded three-way comparison passes eight calls
  under both seeds, with 170 coverage entries, 64 comparison entries and 117
  decisions in 0.308 seconds. The actual captured first insertion also passes
  under both seeds with 822,856 compared endpoint bytes per run. Generic
  allocator behavior remains a supplied captured transition.
- The fast unit tier passes 136 tests, one skipped, in 25.362 seconds.

Checkpoint A remains open: fresh-allocation reconstruction, nonempty structural
mutation, allocation failures/rollback, wrapper and return composition.
Checkpoint B has not begun. The sequence-counter correction remains pending its
landing notice; the failing witness and unrestricted intended Pre/R are
unchanged. No completed-function coverage is added at this checkpoint.

## Four-hour calibration (05:25 UTC)

The charter's first calibration point is reached four elapsed hours after
01:25:17 UTC. Checkpoints A and B remain incomplete. The observed count is
**zero newly completed functions**, so this increment does not yet supply a
new-function completion rate. The strengthened existing lookup, placement
loop, exact reassignment and empty-root physical tail are partial component
results, not substitutes for that measure.

At committed head `7b8b257c`, the increment adds 9,845 Lean lines and deletes
31 across 110 files. Excluding the three generated mutation image/layout
modules gives 8,290 added lines across 107 files. Those figures include
executable reconstruction, tests and supporting proofs; they are neither a
proof-obligation count nor a productivity forecast. New record-reconstruction
lemmas under development at this calibration point are excluded from that
committed-tree count.

Testing delivered useful feedback before universal composition: it exposed the
counter defect, exercised split/failure/rollback cases on a retained heap, and
compared a real captured entry and return. Segment effects also support compact
physical composition: the full empty-root tail composes in 83 lines. The main
remaining cost is proving allocation identity extension, fresh-node decoding,
mutation frames and structural invariants, then composing the complete call.
The earlier normalization failure shows that elaborator costs remain a separate
source of wasted time; the explicit word-representation rewrite repaired that
case without changing its statement.

[AGENT 2026-10-20] Continue the charter's independent insertion obligations.
The evidence justifies further calibration at the first completed function,
but does not yet justify a claim that whole-WireGuard proof cost is viable.
The next concrete obligation is reconstructing and linking a fresh allocated
node from the already tested initialization tail. Nonempty structural paths,
allocation failures/rollback, wrappers and returns follow. The counter fix is
still awaiting the coordinator's landing notice. No precondition restriction,
target weakening or additional environment assumption is introduced to close
that discrepancy.

## Fresh-record reconstruction support (05:29 UTC)

Five modules (429 lines) connect the tested initialization phases to the
actual record decoder: packed header bytes, both key-copy paths, and packed
parent/root publication. `Root.header_copy_core` reconstructs the actual
mirror's `newNode` fields from owner/zero-child facts and the executed copy;
`Root.publish_node` preserves that core, decodes the parent and reads back the
published root word. The allocation-name extension now also preserves all
successfully decoded old parents and node records. No mirror definition was
changed.

These are local lemmas. Their allocation extent, query/table separation and
preceding-phase field facts still need to follow from the complete entry and
allocation resources. They are not new environmental contracts, a narrowed
function precondition or a completed whole-heap reconstruction. The next use
is the existing allocation/attachment phase; structural mutation and complete
function composition remain open.

The default package build, explicit standard-axiom checks, fresh kernel replay
of the enlarged `AllowedipsInsertionSurface` closure and the unchanged printed
trust-surface diff pass. The fast unit tier passes 136 tests, one skipped,
in 24.832 seconds. Ordinary elaboration and syntax failures were repaired
before these checks; no resource-limit increase, KILLED run or timeout occurred
in this step. Disposable normalization probe sources were removed after their
conclusion was recorded. `TrustBase.lean` and the runtime runner are unchanged;
no new external export acceptance is claimed.

## Carry to the fixed-width mirror (06:42 UTC)

The branch is rebased onto main `1f766662`, including campaign 2 and the
fixed-width correction. The pre-rebase dirty proof work was preserved and
restored; no changes were made to main or the private Kraken pin. The
materializer reads `AllowedIps.seq.toNat`; reconstruction decodes the eight
bytes into the actual mirror's UInt64. `reconstruct_fields` proves that its
natural value is exactly the read value, using the existing byte-width bound.
This is an exact representation change, with no non-wrapping Pre or weakened
comparison. The old wrap discrepancy remains documented above.

The preserved reproducer passes all eight cases. For both families and both
undefined-value seeds, sequence `2^64-1` becomes zero on both sides and the
invalid-prefix call returns `-EINVAL` through the ABI return. Ordinary sequence
1 still becomes 2. The binary expectation is unchanged.

Validation on this carry:

- Default binary build: 1,059 jobs, no warnings. Fresh kernel replay of
  `AllowedipsInsertionSurface` passes; explicit axiom prints remain standard.
- The printed trust surface initially failed on exactly the intended
  `seq.toUInt64` reconstruction change. That one-line specification diff was
  reviewed and updated; the subsequent diff passes. `TrustBase.lean` is
  unchanged by this carry.
- Generated execution: 66 insertions and 66 retained-heap lookups, plus 24
  isolated root insertions/lookups; 20 exact and 28 root segments, 3.552 seconds.
- Recorded three-way comparison: eight calls, two seeds, 170 coverage entries,
  64 comparison records and 117 decisions, 0.281 seconds. These are still
  constructed entries with recorded arguments and outcomes.
- Actual captured first-insertion replay: both seeds pass, 254 interpreted
  WireGuard/coverage instructions and 822,856 compared endpoint bytes per run.
  The generic allocator remains a supplied captured transition. The first
  invocation mistakenly supplied a prior result JSON as the input and failed
  decoding; the corrected invocation used `mutation.json`.
- The fast tier first failed because the newly landed fixed-width witness
  executable was missing. After building `leanux-model` and
  `leanux-fixed-width-tests`, all 137 tests pass, one skipped, in 23.653 seconds.

No external export acceptance is claimed for this increment. A and B remain
open, with zero newly completed functions. The counter correction removes a
semantic blocker; fresh-allocation reconstruction and full insertion
composition are still proof work.

## Empty-root reconstruction segment (07:04 UTC)

`Root.initialization_segment` now connects the actual Kraken instructions from
`Add+0x443` to `Add+0x549` to the actual mirror's `emptyInstalled` state for
either address family. It exports the full executable reconstruction, the
segment's output registers and a byte-write frame with the actual root slot.
The fresh node, old nodes, both roots, sequence word, reference counts and all
ownership lists are accounted for. Successful validation of the extended
allocation names follows from the old relation and fresh allocation geometry;
it does not assume the new node already decodes.

This remains a local segment theorem. Its hypotheses include the successful
checked attachment/header/copy/publication phases, fresh allocation resources,
and query and saved-root reads at intermediate phases. Deriving these from
entry and allocator resources, preserving the heap assertion, and composing
the wrappers, nonempty paths, failures and return remain open. The theorem is
not a completed insertion proof. A and B remain open with zero newly completed
functions. No function precondition or environment contract was weakened.

The checkpoint adds thirteen supporting modules, 1,248 lines in total, including
five modules already in progress before the carry. This is not a measurement of
new-function cost. The unused weaker `Root.effect_frame` was removed: its
existential slot lost the association needed by the consumer, whereas the new
segment exports the known-root frame directly. `TrustBase.lean` is unchanged.

Validation: the default binary build passes 1,067 jobs without warnings; explicit
axiom prints contain only the standard three axioms; fresh
`leanchecker --fresh AllowedipsInsertionSurface` passes. The added headline and
definitions were inspected in the printed surface and its subsequent diff
passes. The fast tier passes 137 tests, one skipped, in 24.238 seconds. Runtime
definitions are unchanged since the carry's generated, recorded and actual
capture replays. No external export acceptance is claimed for this increment.

Ordinary elaboration errors were repaired before validation. One recursion-depth
failure came from an incorrectly inferred allocation-name argument and was fixed
by supplying that argument explicitly; no resource limit was raised. No KILLED
run or timeout occurred in this checkpoint.

## Heap-preserving root segment and tested entry resources (07:21 UTC)

The root segment now exports the executable heap assertion as well as full
reconstruction and its byte frame. Its local path condition is that the selected
root is empty; the other root and its trie remain arbitrary. The old nodes keep
their incoming edges, ownership and self-links, and the fresh leaf acquires its
unique root edge and owner membership. This condition identifies the existing
empty-root path, not a restriction of the eventual insertion theorem to empty
tables. The original reconstruction lemma remains available without that path
condition. All other insertion paths remain required.

The proof factors a successful trie traversal through an appended leaf, with
root and child facts extracted from the actual executable heap check. Three
small loop lemmas handle equality on visited elements and unchanged suffixes.
The heap part adds seven modules, 554 lines, plus small shared frame and
allocation-counter lemmas. It does not add an environmental assumption. The
printed surface change was reviewed: the segment's empty-root path premise
and heap postcondition are explicit. `TrustBase.lean` is unchanged.

A new executable post-allocation boundary checks old-world reconstruction,
the selected empty root, owner, saved prefix and root slot, the zeroed 72-byte
allocation, the query, extended allocation validation and local-read/write
separation. The runner evaluates it on actual segment entries, after accounting
for the wrapper's sequence increment. It passes all 28 generated root segments
within 66 insertions/66 retained-heap lookups and 24 isolated root cases, in
3.185 seconds. The recorded three-way comparison passes eight calls under two
seeds, with 170 coverage entries, 64 comparisons and 117 decisions, in 0.269
seconds. The actual captured insertion also passes both seeds, 254 interpreted
instructions and 822,856 compared endpoint bytes each. The allocator is still
a supplied captured transition. These executions test the resource candidates;
they do not prove all kernel callers establish them.

`boundary_fields` extracts the exact checked facts; `allocated_facts` derives
the allocation geometry without assuming a decoded fresh node. The attachment,
copy and publication now each have totality lemmas. Readability persists through
stores, including overlapping copy sources; value preservation remains a
separate frame obligation. `Root.initialization_checked` now composes these
phases directly from the tested boundary: it derives every intermediate read
and successful phase execution, executes the actual Kraken instructions, and
restores full reconstruction, the heap assertion and the byte-write frame. Its
only environment premise is the named decoder agreement. No future phase or
postcondition is assumed. The boundary is still an internal post-allocation cut;
wrapper entry/return, nonempty structural paths, allocation failure/rollback,
and checkpoints A/B remain open. Zero new complete functions are claimed.

The heap segment's default build passes 1,074 jobs, its standard-axiom prints
and fresh `AllowedipsInsertionSurface` kernel replay pass, and its reviewed
printed-surface diff passes. The fast tier passes 137 tests, one skipped, in
23.764 seconds. The copy/publication support also passes a separate fresh
`AllowedipsRootTotalMemory` replay. The final enlarged closure passes the
1,084-job default build without warnings, standard-axiom prints, fresh
`leanchecker --fresh AllowedipsInsertionSurface`, and the reviewed printed
surface diff. The fast tier passes 137 tests, one skipped, in 23.880 seconds.
These last additions are proof-only; the runtime checks above exercised the
same boundary. No external export acceptance is claimed.

At 07:32 UTC, this checkpoint contains seventeen new support modules, 1,245
lines, including the seven heap modules counted above. The source volume is
recorded as a cost diagnostic, not new-function throughput. IPv4 query
separation was corrected from an eight-byte read to the actual four-byte read;
the executable boundary checks four bytes for IPv4 and sixteen for IPv6.
`TrustBase.lean` remains unchanged. The printed headline now uses
`Root.initialization_checked`, replacing the intermediate statement with its
assumed phase executions. The complete function must still establish this
boundary from entry and allocator resources.

Development failures included ordinary syntax/type errors and a default-heartbeat
timeout while Lean tried to infer a natural address from a UInt64 bit-vector
expression. Using the explicit natural-address representation repaired that
timeout without increasing any limit. No KILLED run occurred. The README's
stale description of the wrap witness as still failing was corrected.
