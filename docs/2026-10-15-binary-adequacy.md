# Binary adequacy: work toward milestone 1

Milestone 1 is **not complete**. No function adequacy or transported mirror
property is claimed by the current region lemmas.

## Rule Zero finding 1: a dead index entry retains its peer in the mirror

[USER 2026-10-14] Keep every path, including the dead-peer branch; do not
narrow `Pre_f` to exclude it. The correction is being made on the mirror
lane and will be merged from main. Continue the other regions meanwhile.

Resolution: the owner-shaped repair landed on main at `de62c9d` and was
merged into this branch at `a3c0a44` after the user's landing paste. The
historical finding and its every-path scope remain. Both handshake-owner
and keypair-owner two-lookup regressions now pass: the first clears the
single peer word, and the second takes the null-peer branch. The commands
below exercise the fixed regression on this branch; the original failure
is preserved in the pre-fix history. No dead-peer state was excluded from
Pre or R to obtain this result.

Classification: **mirror defect**. In the pinned ELF,
`wg_index_hashtable_lookup+0xba` (`0xffffffff813a052a`) executes
`mov %rax,(%rbx)`. Linux's `drivers/net/wireguard/peerlookup.c:218` assigns
`entry->peer = wg_peer_get_maybe_zero(entry->peer)`. On the zero-reference
path it stores NULL. The mirror at `a38e3d0` returns `none` without changing
the index entry's nonoptional peer identity.

The witness starts from the recorded prefix of
`d1_wrong_receiver_index_same_bucket`, changes that peer's reference count
to zero, and calls lookup twice for the stored index and handshake kind.
The physical heap is materialized through the oracle's DWARF offsets.
Both decoded lookup and decoded peer-get execute under Kraken, through
their actual RET instructions, with only instrumentation and BH service
summaries. The first call executes 96 instructions and writes NULL into
the entry. The second executes 75 instructions and takes the null-peer
branch. The machine's null-peer outcomes are `[false, true]`; both accepted
mirror calls instead emit `wg_peer_get_maybe_zero.null=0` followed by the
zero-reference decisions. The output slot remains unchanged and both
calls return NULL to the saved entry frame.

This is a synthetic accepted mirror state, **not a claim that the corpus
reaches it at a real kernel entry**. It refutes the proposed every-path
correspondence on that state. Allowing either NULL or the old pointer in
`R` would not repair the second call's decision mismatch.

Reproduce in this worktree (the first command makes a fresh kernel run):

```sh
capped -- python3 binary/run.py
capped -- binary/.lake/build/bin/binary-probe dead-peer .tmp/binary-tv/input.json
```

`Binary.Lookup.peer_write` proves the complete decoded store/test/branch
region at `+0xba`, with a separation frame for all other memory.
`Binary.Lookup.dead_peer_clears_pointer` specializes it to NULL and proves
that the stored pointer is zero and control reaches the miss exit. These
use only `propext`, `Classical.choice`, and `Quot.sound`.

The same finding includes an alias in the owning keypair. Linux's
`queueing.h:68` defines `PACKET_PEER(skb)` as
`PACKET_CB(skb)->keypair->entry.peer`; the mirror reads `Keypair.peer` at
`Receive.lean:396` and `Send.lean:101,255`. Clearing only `IndexEntry.peer`
would leave that alias stale. `KeypairFields.entry_peer_coherent` proves
that the two physical views must read the same word. A second synthetic
two-lookup witness uses a keypair entry and reproduces the same 96/75
instruction runs and differing null decisions, with `Keypair.peer` still
naming the nonnull peer after the binary word is zero:

```sh
capped -- binary/.lake/build/bin/binary-probe dead-keypair .tmp/binary-tv/input.json
```

Mirror peer ID zero in this output is a valid identity whose materialized
address is `0x600000`; it is not the NULL pointer. The alias finding has been
raised to the user for the mirror lane, without a local mirror edit or a
precondition exclusion.

## Current setup and checks

The charter branch was merged first, as requested. All work is on
`task/binary-tv` in `.worktrees/binary-tv`; no integration to main or push.

The fresh three-way test of the recorded nonmatching lookup passed:
45 machine instructions, seven instrumented block-entry PCs, four mirror
decisions, and the lookup's comparison operands. The enclosing differential
check passed one trace, six operations, and 20 operand pairs (18 distinct).
The coverage recorder still deduplicates; this test establishes the recorded
first-occurrence projection, not absence of repeated execution in the kernel.

Kraken's private branch is `task/binary-adequacy`, commit
`eed58b7eda5d1873919616e996bcac205a724dc8`, based on
`8af78062037bc237b341d20252aafd1797c1bcb7`. The source patch is in
`binary/kraken-patches/`; `binary/run.py` reconstructs the private branch
locally and checks its commit and tracked source bytes. The shared checkout
is unchanged.

[AGENT 2026-10-14] Add only the missing forms reached by peer-get: memory
`cmpxchg` and the sign condition (`js`). Register-destination `cmpxchg`
remains an explicit unsupported effect. The memory address and replacement
value are captured before accumulator writeback; failure still requests a
write. Semantics were checked against Intel's SDM, volume 2, CMPXCHG and
Jcc ([official manual](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-2a-manual.pdf)).
Private `Kraken.X64.LookupTests` tests success, failure, accumulator zero
extension, borrow, signed overflow, accumulator-based addressing, parser
rejection and the failed-compare write permission. These are executable
tests, not proof certificates. The sign-branch example is kernel checked.

The composition and generic predicate-transport lemmas in `Execution.lean`
use Kraken's `Eventually`; both have no axioms. They do not supply a
function simulation. `Image.lean` and `Layouts.lean` are generated from the
pinned ELF; the pointer-chain predicate in `Representation.lean` is written
by hand. The complete loop invariant, whole-world relation, callable
precondition with its witness, and function simulation remain unfinished.
No landed mirror result has yet been transported. The proof register's
existing replay-window lag since `247beec` is unchanged by this work.

The successful lookup test (`capped -- python3 binary/run.py --trace
d1_second_response`) now also passes: 111 decoded instructions, 16 ordered
coverage points, seven ordered comparison records and 11 decisions. Both
undefined-value seeds produce the same observables. The decoded peer-get
increments the peer's count; the returned entry and output pointer, saved
registers, stack return and all non-stack materialized bytes agree with the
mirror. The enclosing differential check passes eight operations and 41
operand pairs (32 distinct). This supplies the required three-way test
before proving peer-get; it is not evidence for a universal theorem.

[AGENT 2026-10-14] Add narrow, separate `LEANUX_BINARY_PCS` and
`LEANUX_BINARY_CMP` guest streams for the two pinned ranges. Preserve
repetitions and within-stream order, and isolate one lookup invocation;
leave the ordinary differential streams intact. The first live test's
coverage and decisions agreed but its operand-order comparison failed:
the ordinary remote comparison stream is sorted. The fresh run with raw
comparisons passed. The probe verifies the filter's ranges against the
identity-checked ELF and rejects missing streams or ambiguous invocations.

`RegionExecution.region_eventually` connects the straight-line region
judgment to actual individual fetched instructions. Its continuation proof
distinguishes fallthrough from jumps (including a jump to the next address).
Generated `ImageLayout` lemmas check every region's actual instructions and
lengths against strict address dispatch. `LookupMirror.indexLookup_run`
proves the recursive bucket scan equal to the executable mirror, including
the exact decision prefix and all suffix outcomes. These are ordinary
kernel-checked proofs with the three standard axioms, not a certificate
checker.

Surface work must still account for the result separately from `World`:
NULL versus entry in RAX and the output peer slot. The whole-world relation
must distinguish physical state from supplied environment and execution
history. Some mirror random-key fields deliberately hold unknown-value
placeholders; relating those abstract placeholders cannot assert zero
physical key bytes. An arbitrary unchanged-frame interpretation is useful
for intermediate proofs but is not a completed physical interpretation of
the keypair counters, bitmaps, queues or handshake state. These are open
obligations, not additional assumed conclusions.

The 23 decoded lookup regions now have symbolic instruction facts: fifteen
distinct region proofs and one CALL proof shared by eight identical
instrumentation-call terms (their equality is checked in Lean). All 31
peer-get regions also have instruction facts: eleven singleton trace calls
share one proof, eight comparison/argument setup regions have direct proofs,
and the remaining twelve cover the prologue, epilogue, refcount load and
update, guards and jumps. The loop is not yet composed
through its invariant, peer-get's complete theorem is not yet proved, and
these counts do **not** constitute milestone 1.

The service-readiness fixture now also executes the actual decoded
instrumentation and BH-enable bodies in KCOV_TRACE_PC mode: the successful
lookup takes 506 instructions. It materializes current_task, KCOV mode,
capacity, buffer pointer, context flag and the no-pending-softirq word.
The actual coverage buffer equals the callback-return sequence, all
non-stack/non-coverage bytes match the mirror result, and both seeds agree.
Comparison callbacks execute their real early-return path in this capture
mode; this does not claim a concrete KCOV_TRACE_CMP-mode service run.
This repairs the earlier test fixture's missing service memory, but is
still not a formal `Pre_lookup` witness: that declaration and its proof
remain to be landed together.

Kernel replay with `capped -- lake env leanchecker Execution
RegionExecution MirrorLoop Memory Image ImageLayout Layouts Regions
PeerRegions Prologue BucketEntry Representation Symbolic` passed. The fast
unit tier passed 124 tests with one skip. Reconstructing the private Kraken
commit from the shared base and the committed-format patch produced the
exact pinned hash. No dependency source or global configuration was changed.


## Further work on composition and observations

[AGENT 2026-10-14] Record every actual instruction successor before extracting
correspondence points. Final-state transport alone cannot rule out skipped
or additional decision-point visits. `Binary.history_project` proves that
forgetting this history gives the same strict Kraken instruction execution;
`transport_run` states the generic implication for a complete accepted run.
Neither is the missing function simulation. Service contracts must preserve
this observation discipline too: endpoint framing alone would permit an
unobserved re-entry into an anchored function.

`MirrorHistory` logs the current World at each branch and mirrored call or
return. Its marks cannot accept a supplied World. Erasure of the entire
logged lookup to the current executable lookup is proved, including failures;
the logged loop also has an exact recursive run equation. `LookupObservation`
extracts tags, decisions and comparison operands from actual machine edges,
without receiving the expected mirror run. It rejects unexpected successors
at declared conditional points and preserves repeated visits. The physical
relation between the two histories is still unproved.

`PeerMirror.accepted_count_bound` derives the signed-count bound from an
accepted mirror run. It does not add a positive-refcount entry restriction:
the zero path stays accepted. `PeerGet.increment` proves the actual memory
CMPXCHG succeeds when the loaded word remains unchanged, increments it, and
sets only R15's low byte. Composition still owes the unchanged-word premise
from separation and the single-CPU environment. The binary writes the count
before the mirror's final `setPeer`; the intermediate correspondence must
track that pending update through the saved old value, not assert a false
memory equality.

The physical frame lemma `storeInt_frame` proves equality of every byte
outside the written range. Its read corollary preserves exact values and
unmapped results. This supplies a way to preserve a concrete whole-world
representation; it does not supply that representation by itself. External
inputs, execution-derived history, synthetic names and the three documented
fixture-unknown device secret fields need explicit interpretation separate
from exact physical field equalities.

The kernel's `arch/x86/Makefile` selects eight-byte stack alignment. The
service ABI must follow the compiled kernel's actual register preservation,
stack accesses and return address, without silently assuming the userspace
sixteen-byte entry alignment. The existing region proofs interpret CALL and
RET explicitly and impose no such alignment restriction.


The concrete history comparison passes on the recorded live case (15
semantic/call/return points, 506 instructions with real services) and the
recorded miss case (six points, 191 instructions with real services).
Both also retain the three-way kernel/mirror check using the previously
recorded raw streams. The current history does not yet assert `R` at the
additional stuttering instrumentation, comparison and BH cut points;
those are a separate open composition obligation required by the charter.


The new history, mirror logging, peer-get and memory lemmas passed kernel
replay with `lake env leanchecker` through `capped`; their axiom lists contain
only the three standard axioms. The binary proof target builds. The fast unit
tier again passed 124 tests with one skip (23.94 seconds). The disjoint-write
frame lemma is instantiated for the complete local bucket chain in
`Bucket.frame`. No `Pre_lookup`, concrete satisfying proof, whole-world
simulation, or transported result is claimed by this checkpoint.


[AGENT 2026-10-14] Supplement exact semantic histories with explicit
stuttering-cut alignment. `Image.cutPoints` is generated from the anchored
region entries and their calls, comparisons/tests and returns; service
internals are outside this domain. `CutsAligned` requires each cut's actual
history prefix to observe successfully and match the corresponding prefix
of the fixed source run, and relates the cut state to that prefix's last
source World. It is defined as an obligation, not asserted as a theorem.
Generic prefix lemmas prove that a successful full observation cannot hide
an earlier observation error or change an already emitted prefix.

Read-only observation review found no wrong semantic offsets or branch
outcomes. Its substantive findings are retained as obligations: pending
refcount and entry-pointer updates need explicit phase equations; the
pending refcount cannot rely on RBP after the epilogue restores it; the
logged suffix must change with the mirror correction; anchored cut alignment
and service non-reentry remain to be proved; and return tags require separate
saved-frame/result obligations. The existing epilogue region facts interpret
RET, but their function-level frame premises remain to be discharged.

The DWARF equations now include the physical keypair internal ID, replay
counter and all 128 bitmap words, the three keypair slots, and the global
keypair counter. Array dimensions and element widths come from DWARF and
are checked against the mirror. The replay relation is functional: the same
physical bytes determine the complete mirror counter and bitmap. A separate
frame proof shows that storing NULL into the embedded entry's peer word
preserves those fields, without requiring the entire keypair object to be
read-only. Store membership and the rest of the whole-World relation remain
open.

[AGENT 2026-10-14] Materialize index entries at their actual embedded-object
offsets, rather than allocating independent entry objects. This corrects a
fixture limitation before attempting the formal precondition witness. The
fixture also materializes keypair slots, internal IDs, counters and bitmaps.
The recorded live and miss checks pass again (506 and 191 instructions with
actual services; 15 and six observed points). The two-lookup dead-peer test
still reproduces the defect in 96 and 75 instructions. It is a synthetic
accepted mirror state, not a claim of captured kernel reachability.

The changed proof modules passed kernel replay, with only standard axioms.
The fast tier passed 124 tests with one skip (23.52 seconds). These are
intermediate checks: no `Pre_lookup`, whole-function theorem or transported
property is claimed.

The full local keypair field equations now include both symmetric keys,
their timestamp bit patterns and validity bytes, sending counter, remote
index, initiator flag, refcount and the shared entry peer word. Functionality
and physical frame lemmas are proved. Valid live names make the three slot
identities functional too. These are local components: the complete keypair
store domain cannot be inferred from peer slots or hashed entries, because
packets/workers retain unhashed objects and RCU retirement outlives final
reference release. Its entry relation still needs an explicit lifetime and
ownership account. The fixture rejects out-of-width keypair fields and
inconsistent peer aliases instead of silently truncating or overwriting them.

[AGENT 2026-10-14] Strengthen region facts by finite unrolling of the same
fetched-instruction judgment, preserving every actual successor. The new
`historySteps_eventually` connects these proofs to Kraken's total execution;
the callee-history insertion and observation/cut extension lemmas are proved
once. The index comparison has an exact two-instruction suffix and observer
delta. Five TEST/JE guards also have exact histories, keeping their actual
undefined AF values under Kraken's universal quantifiers. One-instruction
CALL facts can retain their histories through `singleton_region`. These
facts do not yet compose the bucket loop or establish whole-World `R`.

Validation of this checkpoint: `BinaryProofs` and the executable build;
kernel replay of the changed history, observation and keypair modules;
standard axioms only and no forbidden proof-source tokens; the recorded
live/miss three-way tests and both synthetic two-lookup witnesses; 124 fast
tests with one skip (22.82 seconds). The mirror correction is still absent
from the inspected main (`ca6b22e`). Milestone 1 remains open.


## Trust-base and loop-history checkpoint, 2026-10-15

[USER 2026-10-15] Continue from `1738f86`, keep finding 1 and the entire
dead-peer domain, and wait for an explicit landing paste before merging
main. The mirror lane is correcting the owning handshake/keypair entry's
single peer word. Use full parallel Lake builds and QEMU slots 16, with
heavy work capped. No merge or push is authorized. These instructions
override the earlier per-build `-j1` setting and the normal QEMU-slot default
for this task; neither limit was changed globally.

`binary/TrustBase.lean` now names the pinned semantics/image/decoder,
text stability, read-only image, permissions, serialization, ABI, and five
physical service contracts (PC, three comparison callbacks, BH enable).
These are explicit predicates/hypotheses, not globally asserted axioms.
No contract assumes a mirror result, an expected decision sequence, or
preservation of `R`. Coverage contracts specify the actual short-circuit
reads and ordered buffer writes; BH enable includes nested disable counts.
Their footprint excludes the immediate return word. The outer invariant
still owes separation from all live saved stack words, represented objects,
metadata and read-only storage, plus repeated callback readiness.

The ambient decoder is now bound to the generated service listing too.
Review of the draft found a real inconsistency: active comparison states
were admitted by the contracts while two index-only LEAs decoded to missing
instructions. That is repaired in the private Kraken parser at
`e033e3dac812a576881a329b2d4c174364f3d44c`, with its reconstructible patch in
the dependency lock. Existing address semantics are unchanged; the parser
infers address width from the index when no base is present. Parser tests
and native x86 comparison pass. The new `binary-probe service-tests` command
executes 18 callback/BH cases under two undefined-value seeds (648 total
instructions), comparing the entire memory and ABI-preserved frame. It
includes active comparison writes, full buffers, disabled capture, hard-IRQ
early returns and nested BH disable counts.

[AGENT 2026-10-15] Index correspondence by the exact observed event prefix
as well as machine state. A compiler-merged exit emits two mirror decisions
at one physical state, with distinct mirror `steps`; a machine-only
functional relation could not distinguish them. Prefixes now come from
actual observed edges, and concatenation retains their exact cursor. This
is a correction to the obligations, not an established whole-World relation.

The bucket's initial JE and back-edge JNE now have exact instruction-history
and observer equations. The next-pointer load establishes the represented
tail at the pre-guard induction boundary. The mirror scan is proved to
change only `steps` by equality of the complete World record. The stack
lemmas recover all seven pushed helper words after subsequent pushes and
prove slot separation even across modular address wrap. None of these local
facts is the composed loop or helper theorem.

`FixtureKnowledge` separates four documented unknown fields from physical
zero bytes: cookie secret, cookie birthdate, pubkey hash key and global
ratelimiter key. Locations and widths are extracted/checked from DWARF,
including the pointer to the pubkey table and the CU-local ratelimiter
symbol. Origin is computed from fixed fixture lifetime and committed-write
history, not from whether the mirror value happens to be zero. Recorded
values agree exactly; an opaque initial field has the documented mirror
placeholder and mapped physical bytes. Functionality and physical framing
are proved. The complete relation must still justify that incoming history
from actual completed writes: consuming a cookie record is not yet the
field commit, and a recreated device cannot inherit the old device's
knowledge. The ratelimiter key survives uninit. A statement about an opaque
mirror placeholder being zero does not assert physical secret bytes are zero.

Validation: `BinaryProofs` and the executable build with full parallelism;
Lean kernel replay of the changed modules; standard axioms only in the
printed proof dependencies and no forbidden binary proof-source tokens;
recorded live/miss three-way tests (506/191 instructions with actual
services); both synthetic two-lookup defect witnesses; service tests above;
124 fast tests, one skip, 23.197 seconds. The three-way tests reuse the
previous raw kernel streams; no new guest capture or kernel entry snapshot
is claimed. One generator attempt failed because bundle Python lacks
pyelftools; the successful command uses system `/usr/bin/python3`.

Milestone 1 remains open. Whole-World `R`, complete peer-get, loop composition,
`Pre_lookup` together with its satisfying execution witness, and the lookup
simulation/transport theorem are not yet established. No `Pre_lookup` has
landed alone, and no certified-function rate is claimed from the local
instruction-fact count. The milestone report still owes its measured rate,
the trust-base file verbatim, and independent surface review before milestone 2.

## Physical callback invariant and null helper path, 2026-10-15

The named physical predicates added to `TrustBase.lean` are `KcovLayout`,
`KcovMetadata`, `KcovBuffer`, `KcovBufferBytes`, `KcovStorageBytes`,
`KcovMetadataBytes`, `KcovSeparated`, `KcovState` and `KcovStateBytes`.
These are definitions for the eventual entry domain, not new asserted
axioms or a declaration of `Pre_lookup`. They describe runtime metadata,
mapped words, a bounded header and byte separation. No service contract
was strengthened to promise readiness of a later call or preservation of `R`.

[AGENT 2026-10-15] Retain full buffers and capacity zero, and require buffer
storage only in active tracing modes. Disabled tracing follows the actual
early return. Capacity zero still reads the header, so caller-write framing
protects that word separately from the empty callback-write footprint.
This last distinction corrected a draft invariant defect identified during
read-only review; it is not an additional mirror finding.

`KcovInvariant` normalizes the machine-width callback plan to bounded word
offsets, proves planned writes are mapped and inside the buffer, reads back
the new header through all payload stores, and preserves the buffer,
metadata and preempt word. `state_ready` and `state_preserved` derive
repeated-call readiness from these physical facts. `state_frame` proves
that separated caller writes preserve the same state. The proofs include
the exact comparison-record fit boundary and modular address wrap; they
do not assume absolute-address nonwrap.

`KcovExecution` connects these results to the named fetched-instruction
service contracts. `PeerStart`, `PeerCall`, `PeerReturn` and `PeerFinish`
compose the actual prologue, PC calls, six POPs and RET with stack and
callback-state preservation. The saved-register window excludes the
reused callback return slot. `PeerNullEntry.null_entry_to_return` now
executes the complete null-pointer helper path, returning zero, restoring
the entry ABI and framing all other memory. This is one physical path
theorem, not the all-path peer-get theorem or a correspondence-point
simulation. `PeerMirror.accepted_peer_bound` derives the non-null helper's
refcount arithmetic bound from an accepted mirror run; zero counts remain
included and no entry restriction is introduced for finding 1.

Validation: full-parallel `BinaryProofs` and executable build (189 jobs),
kernel replay of all changed proof modules, standard three axioms only in
their printed dependencies, and no forbidden tokens in the 35 binary Lean
sources. The fast tier passed 124 tests with one skip (23.377 seconds).
`capped -- binary/.lake/build/bin/binary-probe peer-null` passed four
configurations with two undefined-value seeds (368 actual instructions),
checking the entire memory and ABI, including high-bit saved registers.
The configurations are PC capture, comparison capture, disabled capture
and zero capacity. These are synthetic executions, not kernel snapshots
or a formal satisfying witness for `Pre_lookup`. Initial heartbeat-limited
proof attempts failed; two exploratory searches were manually terminated.
Only the subsequent completed builds and replay are counted as passes.

Milestone 1 remains open: the non-null live/dead helper paths and its full
correspondence theorem, whole-World `R`, the composed bucket loop,
`Pre_lookup` with its satisfying execution witness, and the lookup
simulation/transport theorem are still outstanding. No milestone rate is
inferred from these supporting lemmas. The mirror-lane landing paste has
not arrived; main has not been merged, and finding 1 is unchanged.

## Nonnull helper execution, 2026-10-15

`PeerDeadEntry.dead_entry_to_return` executes the complete nonnull,
zero-refcount helper path. `PeerLiveEntry.live_entry_to_return` executes the
accepted nonzero-count path, returning the original pointer and establishing
the exact four-byte count increment. Both restore the entry ABI and give
byte-level memory frames. Together with the null case these cover the
physical endpoint cases of an accepted helper run. They do not yet prove
whole-World correspondence at the intervening decision points, and are not
the charter's complete helper simulation theorem.

`PeerComparisons` carries the exact pushed return word as well as callback
readiness and memory framing. `PeerLoad` composes the nonnull guard, physical
refcount load, and initial comparison. `PeerDeadCallbacks` and
`PeerLiveCallbacks` compose the instrumentation sequences and actual branch
instructions. `PeerIncrement` proves the CMPXCHG/comparison composition;
`PeerIncrementFinish` connects it through the signed checks and return.
The old/new sign bounds are ordinary bitvector consequences of the mirror's
accepted-count bound. They are used only on the live path. Zero counts are
admitted by the dead path; finding 1 and its two-lookup witnesses remain
unchanged. No assumption or service contract was added to `TrustBase.lean`.

Validation: full-parallel `BinaryProofs` and executable build passed (199
jobs); `leanchecker` replayed all ten new proof modules; all 159 printed
axiom dependencies in the build were standard, and the source audit found
no forbidden token in 45 binary Lean files. The fast tier passed 124 tests
with one skip (24.227 seconds). `capped --
binary/.lake/build/bin/binary-probe peer-nonnull` passed 21 configurations
with two undefined-value seeds, executing 9,982 instructions. It checks the
entire memory and ABI against explicit expected PC/comparison records,
counts zero, one and `0x7ffffffe`, high-bit saved registers, disabled
capture, both capture modes, empty and partially filled capacities. This
uses actual service bodies and synthetic physical entries; it is not a
captured kernel entry or a formal witness for `Pre_lookup`. Several draft
proof builds failed elaboration and were corrected before the completed
build and replay; none is counted as a pass.

The whole-World audit identifies routing state, pending work and NET_RX
pending state as physical, and work/timer address associations as naming
knowledge derived from execution history. These must not become arbitrary
supplied environment fields. The lookup output slot also needs an ABI
postcondition apart from `R`. These remain implementation obligations.

Milestone 1 is still open: actual-history correspondence for peer-get,
whole-World `R`, the bucket-loop composition, `Pre_lookup` with its
satisfying execution witness, and the function simulation/transport remain.
No function is certified and no R-region rate is inferred from endpoint
supporting lemmas. The milestone report still owes the measured rate and
the trust base verbatim. No mirror landing paste has arrived; no main merge
or push has occurred.

## World decomposition and retained execution history, 2026-10-15

`WorldParts` partitions all 49 current World fields into physical kernel
state, supplied configuration, external fixture state, execution history,
and naming knowledge. Its round-trip theorem checks exhaustiveness, not
physical representation. `PeerMirror.peer_run` gives the exact accepted
source post-world; `peer_parts` proves which of these components change.
`PeerAccepted.accepted_nonnull_to_return` now derives the arithmetic bound
from actual mirror acceptance and covers both nonnull endpoint cases with
the exact final count and return value. It is still an endpoint theorem.

`PeerScalars` generates physical equations for 29 stable peer fields from
DWARF, including the handshake and cookie arrays and serial CPU sentinel.
Its frame theorem admits changes to both the refcount and the embedded
handshake entry's peer word; offset separation is proved modulo 64 bits.
The opaque fixture keys remain governed by `FixtureKnowledge`, not zero
physical bytes. A read-only review found the missing `serialWorkCpu`
equation; it is now included (`none` encodes `nr_cpumask_bits = 1` in this
image). The other 17 peer fields still need their pointer/queue/timer/work
relations; `handshakePending` and `napiScheduled` are physical obligations.
Past user-output fields need actual copy/event provenance, as documented.
These are open representation obligations, not assumptions of a result.

`BucketShape` now states only the index, kind and intrusive-list next fields
read by the loop. It imposes no condition on an entry's peer word. The
owning nullable word and alias equality must be supplied separately by the
whole-world relation after the mirror repair. `tail_iteration` composes the
actual next-node load and guard, preserving the remaining-list invariant
and every instruction successor. `LookupLoads` retains the container-of
cut and all three index-load/argument MOV states, including the comparison
call cut; its kind-guard observation includes the merged `idxFound` event.
The recursive whole-loop theorem remains open.

`ServiceObservation` and `KcovHistory` retain actual callback histories,
prove that their interiors add no anchored observations or cuts, and keep
the return-state relation as an explicit caller obligation. This uses the
existing named no-reentry service contract; no new service contract or
assumption was added to `TrustBase.lean`.

Validation: full-parallel build passed (206 jobs); kernel replay passed
for the eleven changed/new proof modules; all 190 printed axiom dependency
lists were standard, and the source audit found no forbidden token in 51
binary Lean files. The fast tier passed 124 tests with one skip (24.306
seconds). Initial generated framing and instruction-history attempts failed
Lean's resource limits or elaboration; the final frame proof uses named
symbolic-offset lemmas and builds in 1.2 seconds at the default heartbeat
limit. Failed attempts are not counted as passes. Reproduce with
`capped -- lake build BinaryProofs binary-probe` in `binary/`, then
`capped -- lake env leanchecker History Memory WorldParts MirrorPeer
ServiceObservation KcovHistory PeerAccepted PeerScalars Representation
BucketLoop LookupLoads`. Regenerate scalar equations with
`capped -- /usr/bin/python3 binary/generate.py` from the worktree root.

Milestone 1 is not complete. Whole-World physical representation, helper
correspondence at every cut, recursive bucket-loop composition, witnessed
`Pre_lookup`, and the function simulation/transport theorem remain open.
Finding 1 is unchanged; no state was excluded to close it. The milestone
report still owes the measured R-region rate and `TrustBase.lean` verbatim.
No function or transported property is claimed. No main merge or push.

## Node-to-comparison composition, 2026-10-15

`ScanNode.node_to_compare` composes lookup +0x34 through +0x59: four real
instrumentation CALLs and their named service contracts, container subtraction,
the entry guard and the three index-argument moves. It derives the nonnull
entry guard from `BucketShape`, preserves the complete represented bucket,
establishes the loaded source index, and retains the physical scan frame at
every appended anchored cut. `ScanFrame` fixes the stack, query, output,
kind-mask and saved register, and frames memory outside the callback stack
word and KCOV buffer. RBX and RBP are tracked separately as loop temporaries.
This is a physical component, not the whole-World relation or an R-region
certification. Service histories remain in the actual execution; their
interiors have no anchored cuts under the existing named contract.

`LoopSearch.lookup_split` and `finish_split` connect the source prefix/suffix
to the actual logged lookup, preserving failures and every World/checkpoint.
The source equations retain first-index-match termination even for a wrong
kind and emit `idxFound` once. `kindMask_accepts`, `index_source` and
`type_source` derive the source decisions from physical words; allowed-kind
lists may be empty, reordered or duplicated. `LookupType` retains both
actual undefined AF choices at the AND/XOR intermediates. `CallHistory`
executes CALL before applying the service contract and derives readiness
for the next call from the preserved return word.

`BucketShape.frame_reads` now frames exactly next/type/index. Its
`peer_store` theorem permits the owning peer-word update, including NULL,
with explicit separation from other entries' read fields. It does not
pretend to relate that owner word: the mirror repair and owner correspondence
remain open. Finding 1 is unchanged; neither Pre nor R has been narrowed.
No assumption was added to `TrustBase.lean`.

The whole-World review also identified two obligations to retain: consumed
ring slots can contain stale pointers, so object names require lifetimes
separate from current ownership; `serialWorkCpu.getD 1` alone is not a
functional relation (`none` and `some 1` coincide). Its eventual full relation
needs the physical sentinel decoding or a proved reachable-state invariant.
The current peer scalar predicate is explicitly only a component. No
whole-World functionality is claimed for it.

Validation: full-parallel build passed (211 jobs), kernel replay passed for
the eight changed/new proof modules, all 223 printed axiom dependency lists
use only the standard axioms, and the source audit passed for 56 Lean files.
Reproduce with `capped -- lake build BinaryProofs binary-probe`, followed by
`capped -- lake env leanchecker Representation LookupLoads PeerComparisons
CallHistory LookupType LoopSearch ScanFrame ScanNode` in `binary/`.
Initial elaboration attempts failed and were corrected before this build and
replay. The previous 124-test fast-tier result remains the latest; this batch
changes only binary proofs and documentation, not the mirror or runner.

Milestone 1 remains open: recursive loop composition, whole-World physical
representation, peer-get correspondence at every cut, witnessed `Pre_lookup`,
and the function-level simulation/transport theorem. No function is certified,
and no R-region rate is inferred from supporting lemmas. The milestone report
still owes the measured rate and the trust base verbatim. No landing paste
has arrived; no main merge or push.

## Recursive physical scan, 2026-10-15

`ScanSearch.scan_search` now executes both loop headers, arbitrary miss
iterations, and termination at the first matching index (+0x95) or exhausted
bucket (+0x6c). `ScanIteration.scan_miss` executes the callback and actual
next-pointer load, deriving the tail in both current and fixed incoming
memory. Recursion assumes neither a fresh representation nor fresh callback
readiness. Duplicate indices, empty kind masks and dead peers remain in scope;
the scan does not read peer words or test kinds yet.

The result carries exact ordered decision records, their decision tags,
and physical framing at every appended anchored cut. Review found that a
filtered-record equality alone would not exclude extra step=none points;
the final statement additionally proves every emitted point has a decision
record and its matching tag. This does not establish whole-World point
correspondence. The matching case stops before type testing and `idxFound`,
so this is not yet the complete `LoopSearch.searchPrefix` simulation.
`ScanTrace.trans` now composes changed event lists while retaining their
equality to the deterministic observer of the complete actual history.

Validation: full-parallel capped build passed (213 jobs); kernel replay of
`ScanFrame ScanNode ScanIteration ScanSearch` passed; 231 printed axiom
lists used only standard axioms; the source audit passed for 58 Lean files.
Initial elaboration failures were corrected before the final build/replay.
No runtime, mirror, oracle or trust-surface change. The review found no
execution or recursion defect in the physical component.

Milestone 1 remains incomplete. The type suffix needs its own R14 phase
equation after AND, not a restricted accepted mask. Whole-World R, full
helper correspondence, witnessed `Pre_lookup`, and the lookup adequacy and
transport theorem remain open. No new function or R-region is certified;
this support work does not supply the milestone rate. Finding 1 and the
requirement to quote the trust base verbatim at the milestone are unchanged.
No main merge or push; no mirror-lane landing paste has arrived.

## Complete physical bucket loop, 2026-10-15

`BucketScan.bucket_loop` composes the recursive scan with the matched type
suffix, through exhaustion or the first index match of either kind. It
retains the actual instruction history, exact decision records and tags,
and physical frames at every appended cut. `source_bucket_steps` equates
those records with the actual logged mirror prefix. The type suffix exports
the actual +0x9a boundary before R14 is masked, separating the two register
phases without relabeling an earlier state. This is still a physical
component: whole-World R at the corresponding mirror checkpoints is open.

[AGENT 2026-10-15] Relate the ABI kind mask by its two membership tests,
leaving irrelevant bits free. Review identified that equality to a canonical
mask would unnecessarily restrict inputs. `maskKinds_represents` proves
that every 32-bit word has such a source kind-list representation. This is
not a landed entry precondition.

`KeypairFields.entry_peer_store` permits any new owning peer word, including
NULL, while preserving represented keys, counters, replay bitmap and other
scalar fields. It neither interprets the mirror's owner ID nor claims that
a stale alias survives the write. That correspondence still requires the
mirror-lane repair; finding 1 remains recorded and no dead-peer state has
been excluded. No assumption was added to `TrustBase.lean`.

Validation: full-parallel capped build passed (215 jobs), kernel replay of
`Representation LookupType ScanSearch ScanType BucketScan
KeypairRepresentation` passed, 243 printed axiom lists were standard-only,
and the source audit passed for 60 Lean files. The fast tier passed 124 tests
with one skip in 24.670 seconds, with `LEANUX_QEMU_SLOTS=16`. Independent
review found no further defect in these components. Reproduce with the
README build command and `capped -- lake env leanchecker` on those modules.

Milestone 1 remains incomplete: whole-World R, complete helper correspondence,
witnessed `Pre_lookup`, and function simulation/transport remain open. No
function or whole-R region is certified; the support lemmas do not count
toward the milestone's measured region rate. The final milestone report
still owes that rate and the trust base verbatim. No main merge or push; no
mirror-lane landing paste has arrived.


## Landed owner repair and physical components, 2026-10-15

[USER 2026-10-15] Merge main after the `de62c9d` landing paste; retain
finding 1 and dead-peer states without narrowing Pre or R. Abstract peer
retirement using the lifecycle design's section 16.6 no-reader claim, and
report any reader found by the regions. The merge is `a3c0a44`; main itself
was not advanced by this work.

The logged lookup and its decomposition now follow the landed owner shape:
read the nullable word through its handshake/keypair owner, call peer-get,
record its return, reload the current owner, write the result, then record
`idxPeerAlive`. Reloading matters when the handshake owner is the peer the
helper just incremented. `OwnerWord` relates that one word by its embedded
physical address, and `OwnerStore` proves the actual +0xba MOV with its
exact eight-byte frame and the source setters' current-record premises.
NULL and non-NULL stores use the same lemmas. Naming includes represented
zero-count peers; the component does not identify ownership by reading the
nullable word.

The materializer follows those same owner addresses. Both synthetic
regressions execute 96 then 75 instructions, observe null decisions
`[false, true]`, and agree with the complete mirror decision sequences.
The keypair case checks the formerly stale alias as well. These remain
constructed accepted states, not measured reachable kernel entry states.
Review found a separate probe bug: its duplicate manual decision projector
always emitted dead=false at the common final callback. It was removed in
favor of the actual-history observer, which correctly distinguishes null,
dead and live paths. Both recorded comparisons passed again after that fix.

`DeviceScalars` generates 13 stable physical equations from DWARF, including
exact non-placeholder key bytes and signed CPU words. `SerialCpuField`
decodes every 32-bit serial-work CPU word, with the sentinel 1 represented
by `none`; this closes the `none`/`some 1` ambiguity in the older scalar
component when included in R. The four documented opaque fixture fields
remain governed by `FixtureKnowledge`, not by physical-zero requirements.
`ListRing` supplies exact forward and backward links, the closing sentinel,
ordered physical-list functionality and byte framing. Its two instances
relate `Device.peerList` and `Peer.allowedipsList` through DWARF locations.
Store membership and names remain separate: teardown unlinks a peer before
its references disappear, transiently before `numPeers` is decremented,
and may reuse its link in the local dead-peers list. Retired allowed-IPs
nodes share list storage with their RCU callback and need lifetime equations.

`MirrorPeerPoints` gives the exact source worlds at all helper decisions
and return, for null, dead and accepted live counts. `PeerSignHistory`
retains the actual TEST/JS states and universally chosen AF.
`PeerReturnHistory` and `PeerSavedHistory` execute all eight epilogue
instructions with every successor present. `PeerFinishHistory` composes
the final callback and epilogue, proves the exact return observation and
memory framing at every appended cut. `PeerPrologueHistory` records the
six saves, argument copy and actual callback CALL. These are physical and
source components; they do not yet establish R at all helper points.

Review dispositions: the probe projection defect is fixed. Owner naming,
present-store membership, and separation between distinct owning objects
are retained as concrete full-R obligations, not silently assumed by
`OwnerWord.At`. Stores must compose with `OwnerStore.set_*_run` to obtain
the current record. A history-upgrade trap was also identified: the old
`incremented` endpoint abstraction intentionally ignores flags; the exact
CMPXCHG/XOR history must instead carry the actual status and undefined AF.
The existing endpoint proof is unaffected.

The lifecycle no-reader claim still needs a lifetime argument. Inspection
found syntactic post-put reads in the next receive-poll queue iteration and
NAPI completion (`RxData`), and in the next transmit queue iteration (`Data`).
This is not yet a reachable zero-to-reader counterexample: the device's
reference and teardown drains may prove those puts cannot reach zero while
those readers remain. R must establish that condition before treating a
retired peer as inaccessible garbage. The constructed zero-count lookup
peers remain present and readable, as required by the every-path scope.

No trust-base declaration was added or changed by this batch. Whole-World
R still needs the remaining pointer, queue, timer, endpoint/cache and
non-WireGuard equations, then the actual helper pending-count phase and
lookup pending-owner-word phase. The bucket loop's physical invariant must
be lifted through those equations. `Pre_lookup` remains absent until its
concrete formal witness accompanies it; neither a weak placeholder Pre nor
an assumed R-preservation lemma was introduced. Function adequacy and
generic transport are still open, and no function or whole-R region is
certified. The milestone report still owes the measured region rate and
`TrustBase.lean` verbatim. The mirror proof register remains lagging for
ReplayWindow since `247beec`, including its index-lookup framing repairs;
no landed property has been transported by these components.

Validation for this batch: full-parallel capped build passed (226 jobs),
283 printed axiom dependency lists contained only the standard three
axioms, and the source audit passed for 71 Lean files. The generator's six
Lean outputs reproduce byte-for-byte. Initial syntax/elaboration attempts,
including heartbeat timeouts, failed and were corrected before the final
build; none counted as a pass. The fast tier passed 124 tests with one skip
in 37.130 seconds. Both fresh recorded three-way tests passed, then passed
again against those captures after the projector correction: bucket miss
`d1_wrong_receiver_index_same_bucket` (45 summarized-service instructions,
191 with actual services) and live `d1_second_response` (111 and 506).
`LEANUX_QEMU_SLOTS=16` was used. Both two-lookup owner regressions passed
again after the correction. Captures and logs remain ephemeral.

Reproduce the recorded checks with `LEANUX_QEMU_SLOTS=16 capped --
/usr/bin/python3 binary/run.py` and the same command with
`--trace d1_second_response`; reuse a completed capture using `--check`.
Run the two owner regressions using the commands at finding 1. Build with
`capped -- lake build BinaryProofs binary-probe` in `binary/`.

Kernel replay passed for the 16 changed/new proof modules. Reproduce in
`binary/` with `capped -- lake env leanchecker Layouts SerialCpu
DeviceScalars ListRing MirrorLoop MirrorHistory MirrorPeerPoints LoopSearch
PeerSignHistory PeerReturnHistory PeerSavedHistory PeerPrologueHistory
PeerFinishHistory OwnerWord OwnerStore BucketScan`. No main update or push.

Independent read-only review found no correctness defect in the prologue,
shared finish, or circular-list proofs, and rechecked all six list offsets
and widths against DWARF. Its remaining boundaries are explicit: ring
functionality determines addresses, so semantic identities still require
injective lifetime names and membership; the shared finish exports per-cut
memory framing, not per-cut whole-R correspondence or KCOV state by itself.


## Null helper: complete actual history, 2026-10-15

`PeerNullEntryHistory.null_entry_history` composes the actual entry prologue,
first callback, null guard, XOR/JMP clear branch, final callback and saved
RET. The deterministic observer appends exactly null=true and returned,
with the decision tied to its actual successor and the return to the final
machine. Every appended cut has a memory frame against the original entry
(stack saves plus KCOV buffer). `PeerStartHistory` derives body callback
readiness from the actual pushed words. `PeerClearHistory` retains XOR's
universally chosen AF and architectural zero-extension; the null guard
retains TEST's independent AF. No peer read or peer-presence premise is
introduced for the NULL pointer.

This is complete physical/observational composition for one helper path,
not whole-World adequacy or the complete helper theorem. The source-world
relation and permissions still need composition, and dead/live histories
remain open. No trust-base addition or Pre/R restriction.

Validation: capped parallel build passed (230 jobs), all 293 printed axiom
dependency lists were standard-only, the source audit passed for 75 Lean
files, and kernel replay passed for `PeerClearHistory PeerStartHistory
PeerNullHistory PeerNullEntryHistory`. The concrete `peer-null` probe passed
four cases under two undefined-value seeds, 368 instructions total.
Independent read-only review found no correctness/trust defect. Initial
elaboration failures were corrected before the final build. Reproduce with
the README build command, `capped -- lake env leanchecker` on those four
modules, and `capped -- binary/.lake/build/bin/binary-probe peer-null` from
the worktree root. No further mirror/runtime change; the last 124-test fast
tier and recorded three-way checks remain applicable.

Milestone 1 remains incomplete; no function or whole-R region is certified
and no property transported. Its measured rate and verbatim trust base are
still owed at the milestone. No main update or push.


## Dead helper: complete actual history, 2026-10-15

`PeerDeadEntryHistory.dead_entry_history` composes the mapped, nonnull,
zero-refcount helper path from entry through its real RET. The observer
appends exactly null=false, zero=true with operands (0, 0), negative=false,
wraps=false, dead=true, and returned. All five decision states are actual
successors, with memory framing from the original entry at those states
and every appended cut. Both TEST instructions and all XOR instructions
retain their universally chosen undefined flags. The count comes from the
physical memory load; it is not supplied as a desired postcondition.
`PeerLoadHistory` proves the intermediate MOV successor is not a cut and
retains it in the history before LEA establishes the refcount address.
The common nonnull prefix admits every physical UInt32 count.

These are physical/observational components. The live increment history,
whole-World correspondence at every cut, the complete helper theorem, the
lookup theorem and generic transport remain open. Finding 1 stays recorded;
no liveness restriction or change to Pre/R was introduced. The trust base
is unchanged. No whole-R region or function is certified, so these support
lemmas are not counted as completed regions for the milestone's rate.

Validation: capped full-parallel build passed (239 jobs), 327 printed axiom
lists were standard-only, and source audit passed for 84 Lean files. Kernel
replay passed for all nine new modules. The actual-service `peer-nonnull`
probe passed 21 cases under two undefined-value seeds, 9982 instructions.
Initial elaboration failures were corrected before this final build and
are not passes. This proof-only batch changes neither mirror nor runtime;
the previously recorded three-way checks and 124-test fast tier remain
applicable. Reproduce with the README build command, `capped -- lake env
leanchecker PeerCompareHistory PeerDeadSetup PeerDeadCallbacksHistory
PeerDeadSuffixHistory PeerZeroHistory PeerLoadHistory
PeerNonNullPrefixHistory PeerDeadBodyHistory PeerDeadEntryHistory` inside
`binary/`, and `LEANUX_QEMU_SLOTS=16 capped --
binary/.lake/build/bin/binary-probe peer-nonnull` at the worktree root.

Independent read-only review found no correctness defect in the nine new
modules. The end-to-end dead path now discharges the zero-guard arrival and
field-separation obligations. The incoming observer prefix still belongs to
the caller's composition; callback hypotheses, access/environment premises
and whole-World R remain explicit boundaries. Existential decision points
currently export memory frames but not every useful PC/register equation;
strengthening those interfaces later may simplify the R proof.

## Whole-World representation audit: remaining obligations, 2026-10-15

The independent read-only audit identifies these concrete obligations; none
is replaced by an assumed preservation theorem or an extra opaque field:

- The physical index table determines per-bucket order, but not the mirror's
  global insertion order across different buckets. Relate that order to the
  actual prior insertion/unlink/replacement history. Replacement preserves
  position; unlink preserves a stale forward pointer in inactive nodes.
  Embedded owner addresses remain independent of nullable peer-word values.
- Endpoint decoding must use its active union arm. IPv4/IPv6 inactive
  mirror defaults do not require physical zero bytes; stale union tails
  are ordinary. Scope is native-order, flowinfo and addresses network-order.
  The zero-sized endpoint lock shares the handshake's address.
- Cached source family comes from the cached route, not the current
  endpoint. Null cache slots retain stale source/refresh bytes. Route
  generation values are mirror epochs requiring actual routing provenance;
  they are not literal rt_genid/sernum words. A cached route's current device
  can become blackhole_netdev while the historical slot remains. Cache
  storage must not be dereferenced after destruction.
- Slot pointers can temporarily alias, or name a retired allocation absent
  from the mirror's current keypair store. Names must follow lifetimes and
  phases, not require globally distinct slots or positive refcounts.
- Lookup changes only `steps` among non-WireGuard World fields. Its equation
  uses the actual observed machine events appended to the fixed incoming
  observation state. Other observer cursors and supplied environment remain
  fixed during this call; later composition must connect adjacent cursors.
  A copied incoming Kernel is not a physical frame relation.
- The modeled trace task need not be the current KCOV task. File-count and
  inode baselines, fixture external references, and the runner's modeled
  maxFiles value need their explicit abstractions. They cannot silently
  become raw equality to unrelated kernel globals. Task/fd/file, pipe,
  eventfd, epoll, seccomp, socket and pending-work physical equations remain
  necessary even though lookup does not read them.
- Work/timer identities require embedded addresses and lifetime provenance;
  jiffiesLast denotes the last consumed clock observation. The physical
  last_under_load zero sentinel also differs from the placeholder flood
  mode's `some 0`; that mode needs an explicit provenance interpretation.

Field-level footprints should permit legitimate embedding and aliasing.
The final preservation argument must account for the output word, selected
peer count, owner word, stack, KCOV and preempt-count writes. A generic
frame lemma is useful only once its concrete component relations and read
footprints are proved. The audit does not establish whole-World R.


## Live increment and return histories, 2026-10-15

`PeerIncrementHistory.increment_history` retains the seven actual
successors from +0x44 to +0x5b. CMPXCHG's equal-subtraction flags survive
through SETE; SETE changes R15B only. XOR introduces its independently
quantified AF, retained by both following MOVs. The final-state equation
explicitly corrects the older endpoint abstraction's omitted flags.
R15D can contain nonzero upper bytes: the comparison setup copies those
bytes, and the byte callback observes only SIL, as the C instrumentation
requires. No canonical R15 or undefined-flag premise was added.

`PeerIncrementFinishHistory.increment_finish_history` composes that
increment, the byte callback, retry and sign guards, all remaining
callbacks and the actual RET. It derives the final incremented count
using both directions of separation: count writes preserve KCOV state,
and callback writes preserve the count. It exports physical post-increment
memory framing at all four decision points and every appended cut. Those
frames retain the exact incremented word for the future pending-increment
phase of R; the mirror has not updated its peer at those decisions yet.
`PeerLiveZeroHistory` supplies the preceding nonzero guard and PC callback.
The nonnull prefix now exports its derived R13 refcount-address equation.

Independent review found two issues, both corrected and re-reviewed: a
comment overstated count-word preservation without separation, and an
interface discarded the stronger post-increment memory frame needed at
correspondence points. Review found no further correctness defect. The
live function's entry-to-increment composition, whole-World R, accepted
helper theorem, lookup theorem, witnessed Pre and transport remain open.
The trust base is unchanged, dead peers remain admitted, and no whole-R
region or function is certified. Supporting history lemmas do not count
as completed regions in the milestone's rate.

Validation: capped full-parallel build passed (248 jobs); all 351 printed
axiom lists were standard-only; source audit passed for 93 Lean files.
The concrete actual-service nonnull probe again passed 21 cases, two
undefined-value seeds, 9982 instructions. Initial elaboration failures,
a heartbeat/step-limit failure in the monolithic increment attempt, and a
rejected multi-module `leanchecker --fresh` invocation were failures, then
corrected. The increment proof now composes small instruction lemmas.
No KILLED outcome was counted as a pass. Mirror/runtime are unchanged;
the recorded three-way checks and last fast tier still apply.

The trust-gate audit found no forbidden constructs in the 108 project
modules of the then-current proof import closure. Kraken's unsafe concrete
evaluator/pretty-printer and example sorries are outside that closure.
Axiom output alone does not audit explicit theorem hypotheses; the named
contracts and headline statements still require the charter's independent
surface review. Before the milestone, the binary proof roots must join the
separate package's default targets for `lake check`, which checks defaults;
currently its default executable omits many proofs. Source inspection also
suggests the checker's sandbox does not expose the parent-directory path
dependencies. This packaging issue is untested, not a confirmed sandbox
permission failure. The final external gate still remains owed.


Fresh kernel replay passed, including imported declarations, separately for
`PeerLiveZeroHistory` and `PeerDeadEntryHistory`. The live root was replayed
again after the review's strengthened statement. Reproduce in `binary/`
with `capped -- lake env leanchecker --fresh PeerLiveZeroHistory` and a
separate invocation for `PeerDeadEntryHistory`. The concrete command is
`LEANUX_QEMU_SLOTS=16 capped -- binary/.lake/build/bin/binary-probe
peer-nonnull` from the worktree root. No main update or push.


## Complete live helper instruction history, 2026-10-15

`PeerLiveEntryHistory.live_entry_history` now executes the accepted nonzero
helper path from entry through the actual RET, retaining all six decisions,
the original zero-test operands, the exact count increment and restored ABI.
`PeerLiveBodyHistory` and `PeerLiveSuffixHistory` compose the physical load,
nonzero guard, callbacks and increment. Each decision has its physical
memory frame: null/zero against entry memory, later decisions against the
entry memory with the refcount increment. The tail history segment begins
at the increment sequence and includes pre-store successors; only its
anchored cuts are all post-increment. No whole-World conclusion is claimed.

`EqualOutside.storeInt` proves that identical stores preserve an existing
frame, including overlapping or wrapping stores. Independent read-only
review found no correctness defect; its wording caveat about the tail
segment was corrected. All three accepted helper paths now have complete
physical histories. The accepted helper's whole-World theorem, lookup
composition, witnessed Pre_lookup and transport remain open. TrustBase.lean
is unchanged; zero whole-R regions are certified, so these supporting
lemmas do not increase the milestone rate.

Validation: capped full-parallel build passed (251 jobs), 355 printed axiom
lists were standard-only, source audit passed for 96 Lean files, and fresh
kernel replay of `PeerLiveEntryHistory` with imports passed. Reproduce with
`capped -- lake env leanchecker --fresh PeerLiveEntryHistory` in `binary/`.
Initial targeted elaboration failures were corrected before the full build.
The last nonnull concrete probe (21 cases, two seeds, 9982 instructions),
three-way checks and fast tier remain applicable: no runtime or mirror
code changed. No main update or push.


## Concrete heap and fixed-context components, 2026-10-15

`IndexHeap.Chain` relates each bucket head and each embedded node's next
and pprev words to the exact ordered entries. It projects to the existing
`BucketShape` used by the instruction loop, and `Table` supplies that
relation for all 8192 buckets. Framing includes backward links and the
device's table pointer. `Unhashed` leaves stale forward pointers alone.
The mutation fold preserves insertion publication and in-place replacement
exactly; it is a deterministic history parameter, not proof that its events
were executed. Binding it to fixed incoming provenance, owner membership
and injective allocation-lifetime names remains open. No positive-count or
nonnull peer-word restriction was added.

`EndpointHeap` decodes active IPv4/IPv6 fields using the pinned DWARF
layout and exact byte order. AF_UNSPEC alone represents no endpoint;
inactive union bytes need not be mapped or zero. Its frame and functionality
lemmas are proved. IPv4 scope/flowinfo and IPv6 srcIf are canonical mirror
defaults, not physical zero fields. Review confirmed this representation
and noted that canonicality needs an invariant: normal constructors supply
it, but the standalone setPeerEndpoint action accepts arbitrary endpoints.
The relation must not claim to represent those arbitrary values. The
generator checks endpoint field widths and table size and emits the new
offsets; independent capped DWARF re-extraction confirmed them.

`WorldContext` fixes supplied configuration, external fixture state, incoming
history and knowledge for the invocation. Only the decision log advances,
from the actual observer's events. Kernel state is excluded from the context.
Functionality remains conditional on the concrete physical component, which
is not yet complete. The endpoint wrapper binds all events to the observer;
`ObservedPoint` uses an explicit event cursor and the selected actual machine
state, so two source decisions emitted at one compiled edge remain distinct.
Independent review caught this cursor requirement while the wrapper was being
written; it is implemented. Incoming context provenance, actual execution
and ordered cursor composition remain integration obligations, never facts
obtained by copying an incoming World.

Validation: capped full-parallel build passed (254 jobs), all 374 printed
axiom lists were standard-only, and source audit passed for 99 Lean files.
The first DWARF extraction failed on sockaddr's unrelated flexible array;
extraction now asks for its family width specifically. A misspelled Lean
lemma and a missing generated extensionality theorem also failed targeted
builds and were corrected. No failure was counted as a pass. Mirror and
runtime are unchanged, so existing three-way checks and fast-tier results
still apply. TrustBase.lean is unchanged; the whole-World R, witnessed
Pre_lookup, helper/lookup adequacy and transport remain open. Zero whole-R
regions are certified.


Fresh kernel replay passed with imports for `IndexHeap`, `EndpointHeap` and
`WorldContext`, each in its own capped `lake env leanchecker --fresh MODULE`
invocation from `binary/`. The cache audit also confirmed a documented
compatibility abstraction: `dstCacheRecords=false` forces pre-W9 misses and
consumes no cache records (Kernel/Defs.lean and the W8/W9 design). After a
physical stale-slot clear and failed route lookup, that mode can retain a
historical mirror slot. This is not an established Rule Zero mirror defect,
but current-pointer equality is insufficient for R in that mode. Its whole
logical cache needs an explicit history projection. Future send adequacy
still owes actual hit/miss agreement; that projection alone proves none.
No domain restriction was added.


## Physical descriptor-table component, 2026-10-15

`FdHeap` follows the modeled task's files pointer, files_struct fields and
selected fdtable to every descriptor pointer and both modeled bitmaps.
`FdLayouts` is generated by `capped -- /usr/bin/python3 binary/fd_layouts.py`
from the pinned fs/file.c DWARF CU, checking the ELF hash and member widths.
The traced task is independent of KCOV's current task. Descriptor aliases
and open-but-uninstalled reservations remain admitted. Physical bitmap bits
come from little-endian 64-bit words; padding bits are unconstrained.
Framing and functionality are proved; functionality requires occupied
slots' fixed, injective allocation names, including zero-count files that
await deferred fput.

Independent review found no defect. It emphasized that the normal fdtable,
slot array and bitmaps can be embedded inside files_struct, so allocation-
wide disjointness would be incorrect. These components use read footprints.
Allocation validity, lifetime provenance and fdtGeneration's publication
history remain separate obligations. The C's full_fds_bits summary has no
mirror field and is not constrained by this component: it is updated
separately from open_fds and can temporarily disagree. Future FD-function
proofs must account for that phase when they read the summary. Lookup's
no-interleaving premise alone does not establish incoming quiescence.

The audit also confirmed that fixture File fields are explicit abstractions
in Runner.fixtureFile, not uniformly equal to raw f_mode/f_op/f_inode bytes.
Task works can include callbacks other than deferred fput, requiring a
justified ordered projection. Those abstractions and the remaining physical
Kernel components are not supplied by FdHeap.

Validation: capped full-parallel build passed (256 jobs), all 383 printed
axiom lists were standard-only, the two new Lean sources passed the forbidden
construct scan (the prior 99-file audit remains applicable), and fresh kernel
replay of FdHeap with imports passed. Initial structure-update syntax and
array-size proof failures were corrected; none was counted as a pass.
Reproduce replay with `capped -- lake env leanchecker --fresh FdHeap` in
`binary/`. No runtime or mirror change, new assumption, Pre restriction,
whole-R region certification, main update or push.


## Task scalar, credential and limit component, 2026-10-15

`TaskHeap.Fields` now relates the modeled task's blocked/private-pending
signal masks, in_eventfd, PF_KTHREAD, no-new-privileges, TIF_SIGPENDING,
subjective credential pointer and effective CAP_SYS_ADMIN bit, signal
pointer and RLIMIT_NOFILE, and seccomp mode/count/filter pointer. The
selected task remains independent of KCOV current. Other flag bits and
sharing of credential/signal objects stay unrestricted. Task work, exit
state, SIGSYS disposition, filter contents and naming/lifetime coherence
remain separate obligations, not omitted parts of a claimed whole-task R.
`task_layouts.py` extracts checked widths and offsets from the pinned
fs/file{,_table}.c DWARF CUs, including in_eventfd's bitfield location.

The physical frame proof initially failed recursion/heartbeat limits. A
separate read helper and base-tag/Nat offset metadata avoided elaborating
large concrete-address membership expressions; the proof then built in
under a second under the original heartbeat limit. Independent review of
the final code confirmed equivalent read support and the physical field
interpretations. Earlier timeouts were failures, not successful runs.

Validation: capped full-parallel build passed (258 jobs), all 386 printed
axiom lists were standard-only, both new Lean sources passed the forbidden
construct scan (the prior 101-file audits remain applicable), and fresh
kernel replay of TaskHeap with imports passed. Regenerate offsets with
`capped -- /usr/bin/python3 binary/task_layouts.py`; replay in `binary/` with
`capped -- lake env leanchecker --fresh TaskHeap`. No mirror/runtime change,
trust-base addition, domain restriction, whole-R certification, main update
or push. The function-level milestone and its final report remain open.


## Lookup helper-call, result and return histories, 2026-10-15

`LookupPeerCallHistory` executes the owner-word load and actual helper CALL,
including its pushed return address, mapped-stack requirement, frame and
observed call. `LookupResultHistory` executes the owner's write of the
helper result before the NULL test, retaining both branches and each
successor, then separately executes the successful out-parameter store.
`LookupReturnHistory` retains all seven epilogue instructions: MOV of the
entry result into RAX, five saved-register pops, and RET from the actual
stack word. These are physical histories, not whole-World simulation.

Independent review checked the actual oracle disassembly and found no local
defect. Two integration details remain explicit: at +0xc0 the owner word
is already changed while the latest source event is still helper-return,
so R needs a pending-owner phase tied to the actual +0xba return snapshot;
the idxPeerAlive event then commits the source setter. Also, R15 is never
pushed by lookup and must be preserved through its body/helper/services.
The five-word epilogue cannot establish entry R15 equality by itself.
Callback preservation of saved RBP/R13, output readiness, and separation
of stack, object, output and coverage writes remain composition obligations.
Finding 1 stays recorded and no NULL/dead-peer exclusion was introduced.

The task-work audit found no current accepted-path ordering defect. C
detaches an entire batch, whereas the mirror pops one callback at a time.
The physical relation needs the remaining detached tail (from the actual
execution cursor, excluding the current callback) followed by the queued
next batch, not only task->task_works. Current modeled successful fputFinal
callbacks appear to preserve taskWorks: epRemove increments a positive
reference, preserves it through removal and drops a count of at least two;
the other modeled releases contain no deferred fput enqueue. The source
framing theorem is still owed. Unknown/fixture callbacks need concrete
effect classification; filtering their nodes out alone does not prove
order or frame preservation. A future enqueue with a detached tail would
expose the different order and must not be hidden by a premise.


## Lookup entry and bucket header histories, 2026-10-15

`LookupPrologueHistory` and `LookupStackFrame` retain the actual interleaved
register saves/copies and the instrumentation CALL, read back the six saved
words and preserve the original caller return word. `LookupStartHistory`
composes the first callback's actual history and derives body readiness,
argument registers and R15 preservation. Independent review confirmed the
48-byte write footprint. The five saved-register words plus original return
word need preservation through the body; the sixth word below them is
reusable CALL storage and must not be fixed to its first value. The local
start theorem does not by itself protect the original return word against
an overlapping active KCOV buffer; function composition must establish it.

`LookupBucketHistory` retains the BH-count addition, zero-extending query
copy, low-13-bit mask and bucket-head load, with universally quantified AF
and the head read from post-store memory. Independent review confirmed the
actual opcodes and modular flags. A nested BH count remains allowed. For
later enable with RSI=512, readiness checks the updated count's hardirq
mask, not only the original count's: original 0xfe00 carries into that mask
after +512. The named BhEnableReady predicate already expresses the exact
condition; this is a composition obligation, not a mirror defect.

The first start adaptation used a seventh-write frame lemma against the
lookup's six writes and timed out during unification. Correcting that index
closed it under the original heartbeat limit. Other initial elaboration
failures were corrected; no failed attempt was counted as a successful build.


`LookupBucketFrame` derives the updated KCOV state and callback readiness
after the BH store, and frames the linked bucket's physical reads. The
bucket array's separate head-pointer load still needs its own derivation.
`LookupBhHistory` executes argument setup and the actual BH-enable CALL,
derives post-push readiness, and composes the existing named service
contract into the same history. It proves exact count subtraction and the
stack/preempt write footprint. Independent review found no local defect;
balance requires connecting this count to the header's incremented count.

`OwnerPending.PendingAt` is the owner-word phase component for +0xbd/+0xc0/
+0xc3. It takes the old word from the last actual helper-return snapshot,
while current memory holds that snapshot's RAX; the pre-decision prefix
emits no new event. Fixed names determine the old source word uniquely.
This is not a complete control invariant: composition must tie the current
state to the executed result-region prefix and establish its register
equations. Nor does word uniqueness imply uniqueness of the owner or whole
Device. Dead/NULL source words remain admitted.

[AGENT 2026-10-15] Include BinaryProofs in this standalone package's default
targets so a later lake check exports the proof modules as well as the probe.
The mirror package's defaults are unchanged. This corrects the previously
recorded packaging gap; it introduces no semantic assumption.


The owner component also connects the physical result store to both landed
source setters (`handshake_result_at`, `keypair_result_at`). It reloads the
owner from the helper-return World, retaining an aliased increment, and
permits NULL. This is the post-setter word equation; before idxPeerAlive the
matched source World still uses the pending interpretation.

Validation of this batch: capped full-parallel/default build passed (268
jobs), all 433 printed axiom lists were standard-only, all ten new Lean
sources passed the forbidden-construct scan (prior 103-source audit remains
applicable). Separate capped fresh kernel replays passed for
LookupResultHistory, LookupReturnHistory, LookupPeerCallHistory,
LookupPrologueHistory, LookupStartHistory, LookupBucketHistory,
LookupBucketFrame, LookupBhHistory and OwnerPending, including imports. The
final two OwnerPending setter lemmas were then checked by a module replay;
its unchanged imports had already passed fresh replay. Reproduce with
`capped -- lake env leanchecker --fresh MODULE`, one module per invocation
in binary/. The runtime, mirror, pinned image and TrustBase.lean are
unchanged, so the earlier concrete/three-way and runtime-unit results still
apply. No KILLED or timeout was counted as a pass.

Measured checkpoint interval: 6f4d49a at 2026-10-15 04:25:31 UTC through
04:54:28 UTC, 1,737 wall-clock seconds. Whole-World R-region certifications
added: 0; function certifications added: 0; measured certification rate:
0 per hour. The supporting execution/field lemmas above are not substituted
for that count. Milestone 1, its witnessed Pre_lookup, whole-World relation,
complete helper/loop/function simulation and generic transport remain open.
No property is claimed transported. The final milestone report still owes
TrustBase.lean verbatim and the campaign's measured rate.

### Task-work and raw-prefix correspondence checkpoint

`TaskWorkHeap` now represents the attached finite callback chain through
every physical next/function word. Its classification retains non-fput
callbacks and cannot classify an actual `____fput` node as another callback.
Fixed relevant-allocation names determine the file IDs. NULL termination and
the distinct `work_exited` sentinel are separate cases; frames preserve the
queue head and node fields, not callback behavior. The generator follows
anonymous DWARF records/unions, verifies field widths and symbol kinds, and
extracts the pinned task-work offsets and two symbols. The initial generator
failure on the anonymous file union was corrected, not ignored.

This is only the attached queue. During `task_work_run`, the detached suffix
must come from the actual suspended activation and precede newly queued work;
it is not an arbitrary supplied list. An independent source audit found a
proof route to `fputFinal_sameTask` for all accepted runs: epRemove increments
a positive count before its nested fput, which therefore cannot enqueue.
That theorem is not yet checked. Nor would it establish effects for unknown
physical callbacks. No reachable accepted ordering discrepancy was found.

The task-exit audit distinguishes PF_EXITING from the later task-work closed
marker. The mirror never assigns Task.exited=true. A retained child after
Env.childExit is a historical view, including its old seccomp filter ID,
not equality to every current physical field. Actual parent wait4 entry can
precede child exit, so source program position alone cannot determine the
physical lifecycle phase. These need execution-derived equations, not a
new no-exit precondition.

`PeerCountPhase` captures the old operand from the actual successful
CMPXCHG edge, requires the current physical word to be its modular successor,
and clears the pending update at helper RET. The checked one-instruction
composition establishes both the history extension and the old source-count
relation. No positivity or overflow restriction is built into the relation;
acceptance supplies non-overflow at source commit. Service no-reentry proves
phase preservation, while preserving count bytes still needs the existing
write-footprint separation. The full accepted helper composition must prove
the unique outstanding increment and exclude warning paths by acceptance.

[AGENT 2026-10-15] Use the actual raw instruction prefix as an argument of
the final R interface. The early CMPXCHG does not emit a semantic event, so
the semantic-only relation cannot establish its phase provenance.
`ExecutedCorrespondence.AtPoint` selects only an index in the fixed executed
history, at the edge that emitted the current event. Its before/after event
counts distinguish silent repeated states and allow compiler-merged events
to share one raw prefix. Cuts and final correspondence receive their exact
raw prefixes too. The relation will use `PeerCountPhase.scan none`, never a
freely chosen initial pending token. This changes no environment assumption;
the new interface remains a proof obligation, not a claimed simulation.

Independent reviews found no local defects in these three components and
confirmed their integration obligations. A separate SIGSYS audit found that
default/immutable updates preserve unrelated action flags, restorer and mask.
The pinned action starts at sighand+984, with handler/flags/restorer/mask at
offsets 0/8/16/24. The fixture's libc adds SA_RESTORER to SA_SIGINFO; its
handler/restorer addresses need guest-image provenance, not kernel constants.
No reachable fixture defect was found. Task assembly and that disposition
component remain open.

Validation: capped full-parallel default build passed (271 jobs), with 460
printed axiom lists, all standard-only. Fresh kernel replays passed for
TaskWorkHeap, PeerCountPhase and ExecutedCorrespondence with imports; the
final correspondence append/service lemmas then passed a current-module
replay against those unchanged imports. Initial local elaboration failures
were corrected. TrustBase.lean, mirror, runtime and oracle are unchanged.
The previous concrete/three-way tests remain applicable. No KILLED or timeout
was counted as success. No whole-World region/function was certified and no
mirror property was transported; milestone 1 and its witnessed Pre_lookup
remain incomplete.

This checkpoint interval is 3bffac7 at 04:55:01 through 05:11:28 UTC on
2026-10-15: 987 seconds. It adds zero whole-World R regions and zero
functions, a measured certification rate of zero per hour. Supporting field,
phase and composition lemmas are not counted as certified regions.
