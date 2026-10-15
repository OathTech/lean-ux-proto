# Binary adequacy: milestone 1 review handoff

The lookup function theorem and generic transport are now kernel-replayed.
The current result, measured rate, limits and verbatim trust base are in
[the milestone-1 report](#milestone-1-function-theorem-and-review-handoff).
The sections before that report are chronological checkpoints, not current
status. External sandboxed toolchain checking and the coordinator's independent
surface review remain pending; milestone 2 has not started.

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

### Scope correction: WireGuard observations

[USER 2026-10-15] R ranges over the whole World type so WireGuard properties
transport through one relation; exact representation is required only for
the anchored WireGuard read/write surface and landed WireGuard observations.
This includes index owners/tables, peers, keypairs/counters, handshakes,
rings/queues touched by callers and service-callback metadata. Unrelated
task-work, exit, seccomp, credentials, signals, epoll and file-layer fields
are unconstrained. Pre_lookup constrains only reads by lookup and its
callbacks. Keep established components, stop extending non-WireGuard state,
and prioritize bucket-loop composition, a concrete witnessed Pre_lookup and
the function-level simulation; aim the milestone report for today's end.
No merge or push. The earlier whole-World functionality requirement is
superseded for unrelated fields; transport must remain exact on each claimed
WireGuard observation rather than claim arbitrary unrelated predicates.

[USER 2026-10-15] Further strict clarification: R is exactly the frame
relation needed by the simulation, over the WireGuard projection. Each
clause needs an anchored read/write or landed WireGuard observation as its
justification. Untouched state is handled by the binary write footprint and
mirror unchanged-field theorems, never an additional relation clause.
The theorem target and TrustBase are unchanged. Remove unrelated task/file
components from the proof path; they have no planned WireGuard milestone
use and are removed from the tree. Their earlier work remains visible in
the historical checkpoints, not carried as proof prerequisites. This
supersedes the broader relation-assembly direction above. Pre_lookup will
constrain only lookup/callback reads. The day's target remains the witnessed
Pre, function simulation and milestone report, with no merge or push.


### WireGuard frame relation and bucket composition

The strict scope correction is implemented: the task/file/exit/signal
components and exhaustive World partition are removed, including their
unused source-frame consumer and library roots. No physical relation over
unrelated state remains on this proof path. Existing WG field components
remain available for later anchored functions, not lookup prerequisites.

`LookupRelation.project` contains the selected bucket, the selected owner's
nullable peer word and the initially referenced peer's count. The focus is
identity only; it does not copy a source Peer/Device into the environment.
The source projection is separate from incoming steps/rx-section context
and actual raw/event execution histories. Each physical clause has a direct
lookup/helper read/write justification. No device-table-pointer load,
unselected bucket or pprev link is required. BucketShape is a uniform
selected-chain representation, not the minimum individual bytes read by an
early-hit path. Untouched WG observations still need the generic frame
extension before any transported property is claimed.

[AGENT 2026-10-15] Guard the count's pending CMPXCHG phase by the actual
observed active helper call. The raw scan and its machine-captured operand
remain unchanged; the guard removes irrelevant bucket-history obligations
and makes helper return commit ordinary equality. Guard owner-store phase
by both PC and the actual last helper-return tag, so an outer RET into the
same PC range cannot be misclassified.

Independent review exposed a concrete relation counterexample: a source
Some peer ID could map to physical NULL while its refcount word at offset
1056 remained mapped. The mirror would take the nonnull branch and the
machine the null branch. The focused pointer now must be non-NULL. This is
a pointer interpretation condition, not refcount positivity: dead peers
remain in scope, and finding 1 is unchanged. EntryFocus must still be bound
at function entry; it is not assumed to have been initialized by the bucket
preservation theorem.

`LookupBucketSimulation.bucket_simulation` now composes the complete
arbitrary-length bucket segment under its incoming invariant. It retains
the exact source computation, each emitted decision's source World and
actual raw prefix, every anchored silent cut's latest source World, and R
at the endpoint. The first index match terminates even when its kind is
rejected. Physical preservation follows from the executed loop's writes,
including the two phases around the mask-register overwrite. The observer
location lemma distinguishes repeated equal states and compiler-merged
events. The final ScanFrame and raw observations are exported for suffix
composition, resolving a continuation gap identified by review. Review
found no remaining local correctness defect in the composed segment.

This is not entry-to-return adequacy. Entry/header prefix initialization,
EntryFocus, the complete accepted peer-get relation, owner/output/BH/return
composition, Pre_lookup with its concrete witness and the generic untouched
WG frame extension remain open. No function or landed property is certified
by this checkpoint. TrustBase.lean is unchanged and adds no assumptions.
The first satisfying witness will use the recorded same-bucket miss;
its existing concrete materialization ran 191 instructions to return, versus
506 for the recorded live lookup. Both match the mirror and recorded kernel
observations. These are synthesized entry heaps from recorded mirror
prefixes, not captured kernel-entry memory, and are tests rather than proofs.


Validation: capped full-parallel default build passed (267 jobs); all 468
printed axiom lists contain only propext, Classical.choice and Quot.sound.
Fresh kernel replays passed for LookupRelation and LookupBucketSimulation
with their imports. The final export of the already-proved ScanFrame/raw
observations then passed current-module replay against those verified
imports. The new proof files' forbidden-construct scan and git diff check
passed. Local elaboration/generator failures were corrected, not counted as
passes. No KILLED banner or timeout occurred. Mirror/runtime/oracle are
unchanged; the prior concrete and three-way tests remain applicable.

Measured checkpoint interval: 1377184 at 05:11:43 to validation at 05:53:14
UTC, 2026-10-15, is 2491 seconds. It closes one conditional bucket-segment
simulation with all its cuts, but zero witnessed entry-to-return functions.
The certified-function rate remains zero per agent-day; supporting lemmas
and this segment are not substituted for the milestone's certified-region
rate. Milestone 1's function/region rate and verbatim TrustBase report are
still owed when that milestone is reached (or in today's candid status if
it remains incomplete).

### Entry correspondence and callback-domain audit

`LookupEntrySimulation` initializes the actual entry call, then composes
the prologue and first callback and the four-instruction bucket header.
The silent-region lemma derives correspondence from the executed memory
frame at each cut. The head read is obtained from the selected-bucket
relation after the actual BH-count store. Both wrappers retain the raw
tail and every cut's memory frame for later untouched-WG transport; review
caught that those facts had initially been discarded by the wrappers.
These are conditional supporting regions, not an entry-to-return theorem.

The relation definitions now live in `LookupProjection`, and the raw
count-phase definitions in `PeerCountState`, without changing their
bodies. This permits the eventual witnessed entry declaration to import
the definitions without a circular dependency on its own proof lemmas.
`TrustBase.lean` remains unchanged; `Pre_lookup` is not yet declared.

The precondition audit found that the existing uniform KCOV invariant
requires all metadata even when the callback would skip some reads.
At the recorded preempt counts 0 and 512, softirqEnabled is never read.
Simply weakening readiness to the current count is insufficient: modular
addition can change the gating. For example, incoming 0x00fffe00 rejects
tracing, while adding 512 produces 0x01000000 and enables metadata reads.
The entry domain must cover both actual callback contexts without forcing
the count to zero. Full selected-bucket shape is likewise a uniform field
representation, not the exact path's minimum byte-read set. These domain
questions remain explicit; no dead-peer state has been excluded.

Validation for the entry checkpoint: capped default build passed (270
jobs), with standard-only axioms for all seven new declarations. Fresh
kernel replay passed with the imported proof path; the final frame-export
change also passed kernel replay against those verified imports. No runtime or mirror change was
made. No KILLED banner or timeout occurred. Function certification and
transport remain at zero; the witnessed Pre and complete helper/function
composition are still required.


### Witnessed entry domain, 06:48 UTC checkpoint (milestone 1 incomplete)

[USER 2026-10-15] R is a frame relation over the WireGuard projection
needed by anchored reads/writes and landed WireGuard observations. Unused
World fields are outside it by construction; untouched WireGuard fields
require their own frame theorem. The stricter scope supersedes the earlier
whole-World representation interpretation. Finding 1 remains recorded;
neither dead peers nor NULL owner words are excluded to accommodate it.

`TrustBase.Pre_lookup` now names the physical entry obligations, with
`LookupWitness.witness_pre` proving a concrete inhabitant. Its callback
metadata requirements follow the actual gates in both modular preempt-count
contexts. Comparisons need buffer metadata only on a nonempty selected
bucket; disabled callbacks need no buffer mapping. The stack depth is six
words for a miss and thirteen when the helper is called, including the NULL
helper path. Output mapping is conditional on an accepted live result, not
an entry positivity or count-bound assumption. Separation is an explicit
allocation discipline, not a claim to admit every safe x86 alias. The
selected bucket has a uniform complete chain representation.

The satisfying fixture is synthesized from the read projection of operation
3 of `d1_wrong_receiver_index_same_bucket`. It is not captured kernel-entry
memory or a claimed reachable whole World. Its unrelated fields are concrete
inhabitants; even the unread handshake owner object is absent. The exact
Lean state satisfying Pre executes 191 instructions to the return, preserves
callee-save registers, and emits six correspondence points. Both undefined
value seeds agree. The prerequisite three-way probe compares the recorded
kernel coverage/operands, reference Kraken execution and mirror decisions;
the exact witness test then compares its smaller materialization with that
reference execution and the same source read projection. Both commands must
succeed, in order; input.json alone is insufficient because a failed probe
can still write it:

```sh
LEANUX_QEMU_SLOTS=16 capped -- python3 -B binary/run.py --check .artifacts/check/binary-tv-20261015-024459 --trace d1_wrong_receiver_index_same_bucket
cd binary
LEANUX_QEMU_SLOTS=16 capped -- lake env lean LookupWitnessTest.lean
```

Validation: both commands passed, the full-parallel capped default build
passed (288 jobs), the witness and its supporting declarations printed only
propext, Classical.choice and Quot.sound, and fresh kernel replay of
LookupWitness with its imports passed. The changed proof path contains none
of the forbidden proof escapes. The non-sandboxed external lake-check gate
has not been run; no milestone or integration claim is made.

Earlier concrete-memory elaboration attempts failed: two large attempts
were interrupted, and multiple 8 GiB capped attempts exited 137 with KILLED
banners. These are failures, not passes. The fix was to prove mapping over
an abstract buffer before applying it to the concrete memory, preventing
elaboration from unfolding the entire map. The successful full witness
check then completed without increasing that 8 GiB cap. Dirty states were
preserved to local snapshot refs before further edits.

Measured interval: checkpoint 9d2886d at 06:09:20 to final validation at
06:48:56 UTC is 2376 seconds. This interval closes one witnessed physical
entry declaration, zero new complete simulation regions and zero functions.
Certified-region and certified-function rates for this interval are both
zero per agent-day; the witness was hand-finished, not generated. The earlier
bucket and entry/header simulations remain conditional supporting regions.
No landed WireGuard property is yet transported to the binary.

The main remaining work is explicit: replace the stronger callback proof
invariant with the conditional entry-domain invariant; retain the actual
service no-reentry fact through helper histories and prove its pending
CMPXCHG phase at all cuts; compose the helper, owner store, output, BH and
return with the entry/header/bucket simulation; and prove the generic frame
extension and function-level theorem. Read-only review found no further
concrete entry-domain contradiction, but did identify those proof-interface
and transport obligations. This checkpoint is not the independent completed
milestone-1 surface review required before milestone 2.

### Current TrustBase.lean, verbatim at the witnessed-entry checkpoint

This is the current surface for review, not a claim that the complete lookup
theorem has been proved. No project axiom was added; declarations express
named hypotheses and physical predicates.

```lean
import History
import Image
import ServiceImage
import Memory
import LookupProjection

/-! Named trust surface for the pinned lookup proof, under construction.
    These are explicit hypotheses, not globally asserted facts. No declaration
    here assumes the lookup result, a region's R-preservation, or a mirror run.
    Pre_lookup is accompanied by its concrete satisfying witness.
    The final milestone report must reproduce this file verbatim.

    External interpretation: binutils 2.42 supplied the literal AST and DWARF
    layouts from the ELF below. Lean checks execution of those terms, not the
    binutils decoder, DWARF producer, SHA computation or correspondence of
    Kraken's model with x86 hardware. The loader checks identity and branch
    encodings. Mutable runtime globals are NOT assumed equal to ELF initial
    bytes at a function entry; their current values belong in Pre_lookup.
-/
namespace Binary.TrustBase

def krakenCommit : String := "e033e3dac812a576881a329b2d4c174364f3d44c"
def kernelIdentity : String := "6b2018b9"
def elfSha256 : String := "16c346209885db6c610d4aa126c6eb30f5d3c02f0498d95e606473945f648774"
def decoderVersion : String := "GNU objdump (GNU Binutils for Ubuntu) 2.42"

local instance : Labels := Image.linkedLabels

/-- The partial linked decoder for both anchored functions and all reached
    service bodies. A rejected instruction remains a failing fetch; neither
    its semantics nor successful execution is assumed by this definition. -/
def pinnedFetch (pc : Int64) : Option Decoded :=
  (Image.fetch pc).orElse (fun _ => ServiceImage.fetch pc)

/-- The ambient instruction image is this fixed ELF-derived listing,
    including service bytes. This is the external bytes-to-AST assumption. -/
def WholeImageDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  fetch = pinnedFetch

/-- The ambient decoder agrees with the pinned literal instructions/lengths.
    Interpreting those literals as this ELF is the external decoding assumption. -/
def AnchoredDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, Image.fetch pc = some instruction → fetch pc = some instruction

/-- No alternatives/static-key text change in a certified anchored range. -/
def AnchoredTextStable (fetchAt : Nat → Int64 → Option Decoded) : Prop :=
  ∀ time pc instruction, Image.fetch pc = some instruction → fetchAt time pc = some instruction

/-- Read-only image bytes remain the linked bytes. `linked` is the loader's
    fixed ELF projection; it is not chosen independently at each proof point. -/
def ReadOnlyImage (linked : Mem 64) (readOnly : BitVec 64 → Prop) (memory : Mem 64) : Prop :=
  ∀ address, readOnly address → memory.get? address = linked.get? address

/-- External paging/access permissions, absent from Kraken MachineState. -/
structure Permissions where
  read : BitVec 64 → Width → Prop
  write : BitVec 64 → Width → Prop
  execute : Std.Rco Int64 → Prop

/-- Kraken's All grants permission requests. This separate premise makes
    that grant explicit for every effect, including every undefined outcome. -/
def AccessAllowed (permissions : Permissions) : Effects → Prop
  | .done _ => True
  | .unimplemented _ | .gp_unaligned .. | .nonmem_load .. | .nonmem_store .. => False
  | @Effects.undefined α _ next => ∀ value : α, AccessAllowed permissions (next value)
  | .require_read_access address width next =>
      permissions.read address width ∧ AccessAllowed permissions (next ())
  | .require_write_access address width next =>
      permissions.write address width ∧ AccessAllowed permissions (next ())
  | .require_exec_access pc next =>
      permissions.execute pc ∧ AccessAllowed permissions (next ())

/-- Every actually executed instruction has its requested accesses granted;
    the final return destination is not itself executed by this run. -/
def RunAccessAllowed (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (history : List MachineState) : Prop :=
  ∀ s ∈ history.dropLast, ∃ decoded, fetch s.pc = some decoded ∧
    permissions.execute ⟨s.pc, s.pc + .ofNat decoded.size⟩ ∧
    AccessAllowed permissions
      (decoded.instruction.interp s.data ⟨s.pc, s.pc + .ofNat decoded.size⟩
        (fun d => .done ⟨d, s.pc + .ofNat decoded.size⟩) (fun pc d => .done ⟨d, pc⟩))

/-- The environment places no interrupt, preemption or competing CPU action
    inside this anchored call; the records place such actions between calls. -/
structure SerializedEnvironment (onlineCPUs : Nat) (externalActions : List Nat) : Prop where
  singleCPU : onlineCPUs = 1
  noInterleaving : externalActions = []

/-- Kernel ABI: the stack word is the actual CALL return address. Eight-byte
    alignment follows this kernel's compiler flags, not a userspace ABI guess. -/
def EntryFrame (s : MachineState) (returnAddress : UInt64) : Prop :=
  s.data.regs.rsp.toNat % 8 = 0 ∧
  s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8 = some (returnAddress.toNat : Int)

/-- Only ABI-preserved registers are constrained; caller-save registers and
    flags may change. The callee has consumed the actual return-address word. -/
def Returned (entry final : MachineState) (returnAddress : UInt64) : Prop :=
  final.pc = .ofBitVec returnAddress.toBitVec ∧
  final.data.regs.rsp = entry.data.regs.rsp + 8 ∧
  final.data.regs.rbx = entry.data.regs.rbx ∧
  final.data.regs.rbp = entry.data.regs.rbp ∧
  final.data.regs.r12 = entry.data.regs.r12 ∧
  final.data.regs.r13 = entry.data.regs.r13 ∧
  final.data.regs.r14 = entry.data.regs.r14 ∧
  final.data.regs.r15 = entry.data.regs.r15

/-- Service internals emit no anchored observation or cut. The final state
    may return to an anchored address; it is deliberately not excluded. -/
def NoAnchoredReentry (history : List MachineState) : Prop :=
  ∀ s ∈ history.dropLast, Image.fetch s.pc = none

/-- A service contract uses the same fetched-instruction execution as the
    function proof. Its readiness and write footprint are physical predicates;
    their concrete instantiations must be part of the witnessed entry domain. -/
def ServiceReturns (fetch : Int64 → Option Decoded) (address : Int64)
    (ready : MachineState → Prop) (writes : MachineState → BitVec 64 → Prop)
    (effect : MachineState → MachineState → Prop) : Prop :=
  ∀ s returnAddress, s.pc = address → ready s → EntryFrame s returnAddress →
    Eventually (historyStep fetch)
      (fun t => Returned s t.machine returnAddress ∧
        EqualOutside (writes s) s.data.dmem t.machine.data.dmem ∧
        effect s t.machine ∧ NoAnchoredReentry t.history)
      ⟨s, [s]⟩

def preemptCountAddress : BitVec 64 := .ofNat 64 0xffffffff81cc85c8
def currentTaskAddress : BitVec 64 := .ofNat 64 0xffffffff81cc85c0
def softirqPendingAddress : BitVec 64 := .ofNat 64 0xffffffff81cc85e0

inductive KcovKind where
  | pc | cmp4 | constCmp4 | constCmp1
  deriving DecidableEq

structure WordWrite where
  address : BitVec 64
  value : BitVec 64

def load64 (memory : Mem 64) (address : BitVec 64) : Option (BitVec 64) :=
  (memory.loadInt address 8).map (.ofInt 64)

def load32 (memory : Mem 64) (address : BitVec 64) : Option (BitVec 32) :=
  (memory.loadInt address 4).map (.ofInt 32)

/-- Physical callback metadata, fixed during an anchored call except for the
    separately balanced preempt count. Capacity is a count of 64-bit words. -/
structure KcovLayout where
  task : BitVec 64
  area : BitVec 64
  capacity : BitVec 32
  mode : BitVec 32
  softirqEnabled : BitVec 32

/-- Exact runtime metadata reads, not the ELF's initial global bytes. -/
def KcovMetadata (layout : KcovLayout) (memory : Mem 64) : Prop :=
  load64 memory currentTaskAddress = some layout.task ∧
  load32 memory (layout.task + 0x6e0) = some layout.mode ∧
  load32 memory (layout.task + 0x6e4) = some layout.capacity ∧
  load64 memory (layout.task + 0x6e8) = some layout.area ∧
  load32 memory (layout.task + 0x704) = some layout.softirqEnabled

/-- Mapped buffer and bounded runtime header. A full buffer is allowed; no
    callback is required to have room for a record. This predicate says
    nothing about the peer state or the lookup result. -/
def KcovBuffer (layout : KcovLayout) (memory : Mem 64) : Prop :=
  (∀ word < layout.capacity.toNat,
    (memory.loadInt (layout.area + .ofNat 64 (8 * word)) 8).isSome = true) ∧
  ∃ count : Nat, count ≤ layout.capacity.toNat ∧
    load64 memory layout.area = some (.ofNat 64 count)

def KcovBufferBytes (layout : KcovLayout) : BitVec 64 → Prop :=
  InRange layout.area (8 * layout.capacity.toNat)

/-- Storage read by an active callback. Even capacity zero still requires
    the header; caller writes must preserve it as well as the buffer words. -/
def KcovStorageBytes (layout : KcovLayout) (address : BitVec 64) : Prop :=
  InRange layout.area 8 address ∨ KcovBufferBytes layout address

def KcovMetadataBytes (layout : KcovLayout) (address : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 address ∨
  InRange (layout.task + 0x6e0) 4 address ∨
  InRange (layout.task + 0x6e4) 4 address ∨
  InRange (layout.task + 0x6e8) 8 address ∨
  InRange (layout.task + 0x704) 4 address

/-- Physical disjointness from protected memory (metadata, live stack and
    represented objects). Readiness is proved from this, not assumed at
    every callback. The caller chooses the actual protected footprint. -/
def KcovSeparated (layout : KcovLayout) (protectedBytes : BitVec 64 → Prop) : Prop :=
  ∀ address, KcovBufferBytes layout address → ¬protectedBytes address

/-- Physical state carried between callbacks. Disabled tracing requires no
    mapped coverage area; the mode field itself still belongs to the task. -/
def KcovState (layout : KcovLayout) (preempt : BitVec 32) (memory : Mem 64) : Prop :=
  KcovMetadata layout memory ∧
  load32 memory preemptCountAddress = some preempt ∧
  (layout.mode = 2 ∨ layout.mode = 3 → KcovBuffer layout memory)

/-- Bytes that caller stores must preserve. Buffer storage is needed only
    in an active mode; metadata and preemption state are always physical. -/
def KcovStateBytes (layout : KcovLayout) (address : BitVec 64) : Prop :=
  KcovMetadataBytes layout address ∨ InRange preemptCountAddress 4 address ∨
    ((layout.mode = 2 ∨ layout.mode = 3) ∧ KcovStorageBytes layout address)

/-- Physical KCOV callback specification, with the actual early-return read
    dependencies and machine-width arithmetic. It is not a proof checker. -/
def KcovPlan (kind : KcovKind) (s : MachineState) : Option (List WordWrite) := do
  let memory := s.data.dmem
  let preempt ← load32 memory preemptCountAddress
  let returnPC ← load64 memory s.data.regs.rsp.toBitVec
  let task ← load64 memory currentTaskAddress
  if preempt &&& 0xff0100 != 0 then
    if preempt &&& 0x100 == 0 || preempt &&& 0xff0000 != 0 then return []
    let softirqEnabled ← load32 memory (task + 0x704)
    if softirqEnabled == 0 then return []
  let mode ← load32 memory (task + 0x6e0)
  if mode != (if kind = .pc then 2 else 3) then return []
  let area ← load64 memory (task + 0x6e8)
  let capacity ← load32 memory (task + 0x6e4)
  let count ← load64 memory area
  if kind = .pc then
    let next := count + 1
    if next.toNat ≥ capacity.toNat then return []
    return [⟨area, next⟩, ⟨area + 8 * next, returnPC⟩]
  else
    let slot := 4 * count
    let ending := 8 * slot + 40
    if 8 * (capacity.setWidth 64) < ending then return []
    let tag : BitVec 64 := match kind with
      | .pc => 0
      | .cmp4 => 4
      | .constCmp4 => 5
      | .constCmp1 => 1
    let arg1 := if kind = .constCmp1 then (s.data.regs.get (.low .rdi .W8)).setWidth 64
      else (s.data.regs.get (.low .rdi .W32)).setWidth 64
    let arg2 := if kind = .constCmp1 then (s.data.regs.get (.low .rsi .W8)).setWidth 64
      else (s.data.regs.get (.low .rsi .W32)).setWidth 64
    return [⟨area, count + 1⟩, ⟨area + ending - 32, tag⟩,
      ⟨area + ending - 24, arg1⟩, ⟨area + ending - 16, arg2⟩,
      ⟨area + ending - 8, returnPC⟩]

/-- Planned destinations are mapped and do not overwrite the return word.
    Separation from all represented objects is an additional entry obligation. -/
def KcovReady (kind : KcovKind) (s : MachineState) : Prop :=
  ∃ stores, KcovPlan kind s = some stores ∧
    ∀ write ∈ stores,
      (s.data.dmem.loadInt write.address 8).isSome = true ∧
      ∀ address, InRange write.address 8 address → ¬InRange s.data.regs.rsp.toBitVec 8 address

def KcovWrites (kind : KcovKind) (s : MachineState) (address : BitVec 64) : Prop :=
  ∃ stores, KcovPlan kind s = some stores ∧
    ∃ write ∈ stores, InRange write.address 8 address

/-- Exact callback stores keep repeated-call buffer readiness provable;
    allowing arbitrary corruption of the coverage buffer would not suffice. -/
def KcovEffect (kind : KcovKind) (before after : MachineState) : Prop :=
  ∃ stores, KcovPlan kind before = some stores ∧
    after.data.dmem = stores.foldl
      (fun memory write => memory.storeInt write.address 8 write.value.toInt) before.data.dmem

/-- KCOV PC callback: only its physically planned stores may occur. -/
def TracePcContract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)

/-- KCOV variable/variable 32-bit comparison callback. -/
def TraceCmp4Contract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3e80) (KcovReady .cmp4) (KcovWrites .cmp4) (KcovEffect .cmp4)

/-- KCOV constant/variable 32-bit comparison callback. -/
def TraceConstCmp4Contract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3f00) (KcovReady .constCmp4)
    (KcovWrites .constCmp4) (KcovEffect .constCmp4)

/-- KCOV constant/variable 8-bit comparison callback used by peer-get. -/
def TraceConstCmp1Contract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3ec0) (KcovReady .constCmp1)
    (KcovWrites .constCmp1) (KcovEffect .constCmp1)

/-- The actual no-work BH-enable path, including nested disable counts.
    The softirq word is needed only on the branch that reads it. -/
def BhEnableReady (s : MachineState) : Prop :=
  ∃ count : BitVec 32,
    s.data.dmem.loadInt preemptCountAddress 4 = some (count.toNat : Int) ∧
    count &&& 0x000f0000 = 0 ∧
    ((count + 1 - s.data.regs.get (.low .rsi .W32)) &&& 0x00ffff00 = 0 →
      s.data.dmem.loadInt softirqPendingAddress 2 = some 0) ∧
    ∀ address, InRange preemptCountAddress 4 address → ¬InRange s.data.regs.rsp.toBitVec 8 address

/-- BH enable balances the actual low-32-bit count argument, modulo 2^32.
    Readiness must justify that its softirq path runs no pending work. -/
def BhEnableContract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810732c0) BhEnableReady
    (fun _ => InRange preemptCountAddress 4)
    (fun before after => ∀ old : BitVec 32,
      before.data.dmem.loadInt preemptCountAddress 4 = some (old.toNat : Int) →
      after.data.dmem.loadInt preemptCountAddress 4 =
        some ((old - before.data.regs.get (.low .rsi .W32)).toNat : Int))

/-- Whether the actual callback reads softirqEnabled before its mode test. -/
def LookupSoftRead (preempt : BitVec 32) : Prop :=
  preempt &&& 0xff0100 ≠ 0 ∧
  ¬(preempt &&& 0x100 = 0 ∨ preempt &&& 0xff0000 ≠ 0)

/-- The callback reaches its mode read only after the preemption/softirq gate. -/
def LookupModeRead (coverage : KcovLayout) (preempt : BitVec 32) : Prop :=
  if preempt &&& 0xff0100 ≠ 0 then
    ¬(preempt &&& 0x100 = 0 ∨ preempt &&& 0xff0000 ≠ 0) ∧ coverage.softirqEnabled ≠ 0
  else True

/-- PC callbacks occur before and after BH-disable. Comparisons occur only
    with a nonempty selected bucket, after the actual modular increment. -/
def LookupBufferNeeded (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) : Prop :=
  (coverage.mode = 2 ∧ (LookupModeRead coverage preempt ∨ LookupModeRead coverage (512+preempt))) ∨
  (coverage.mode = 3 ∧ v.bucket ≠ [] ∧ LookupModeRead coverage (512+preempt))

/-- Only callback metadata reached in one of this lookup's two contexts.
    Unused layout values impose no equality on memory. The active coverage
    allocation is mapped uniformly; a full buffer is permitted. -/
def LookupCoverageAt (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (memory : Mem 64) : Prop :=
  load64 memory currentTaskAddress = some coverage.task ∧
  ((LookupSoftRead preempt ∨ LookupSoftRead (512+preempt)) →
    load32 memory (coverage.task+0x704) = some coverage.softirqEnabled) ∧
  ((LookupModeRead coverage preempt ∨ LookupModeRead coverage (512+preempt)) →
    load32 memory (coverage.task+0x6e0) = some coverage.mode) ∧
  (LookupBufferNeeded coverage preempt v →
    load32 memory (coverage.task+0x6e4) = some coverage.capacity ∧
    load64 memory (coverage.task+0x6e8) = some coverage.area ∧ KcovBuffer coverage memory)

def LookupMetadataBytes (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 a ∨
  ((LookupSoftRead preempt ∨ LookupSoftRead (512+preempt)) ∧ InRange (coverage.task+0x704) 4 a) ∨
  ((LookupModeRead coverage preempt ∨ LookupModeRead coverage (512+preempt)) ∧ InRange (coverage.task+0x6e0) 4 a) ∨
  (LookupBufferNeeded coverage preempt v ∧
    (InRange (coverage.task+0x6e4) 4 a ∨ InRange (coverage.task+0x6e8) 8 a))

def LookupCoverageWrites (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  LookupBufferNeeded coverage preempt v ∧ KcovBufferBytes coverage a

def LookupServiceBytes (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  LookupMetadataBytes coverage preempt v a ∨ InRange preemptCountAddress 4 a ∨
  (LookupBufferNeeded coverage preempt v ∧ KcovStorageBytes coverage a)

/-- The helper is called for a selected owner even when its peer word is NULL. -/
def LookupStackWords (c : LookupRelation.Config) : Nat := if c.focus.owner.isSome then 13 else 6

def LookupStackWrites (c : LookupRelation.Config) (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (8*LookupStackWords c)) (8*LookupStackWords c)

def LookupLiveStack (c : LookupRelation.Config) (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (8*LookupStackWords c)) (8*LookupStackWords c+8)

def LookupBucketBytes (c : LookupRelation.Config) (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  InRange (c.table + .ofNat 64 (8*(c.query%8192))) 8 a ∨
  ∃ e ∈ v.bucket, BucketShapeReads (LookupRelation.ownerAddress c e.owner) a

def LookupOwnerBytes (c : LookupRelation.Config) (a : BitVec 64) : Prop :=
  ∃ owner, c.focus.owner = some owner ∧ InRange (LookupRelation.ownerAddress c owner) 8 a

def LookupCountBytes (c : LookupRelation.Config) (a : BitVec 64) : Prop :=
  ∃ pid, c.focus.peer = some pid ∧ InRange (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 a

def LookupDataWrites (c : LookupRelation.Config) (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  LookupOwnerBytes c a ∨ ((∃ n, v.count = some n ∧ n ≠ 0) ∧ LookupCountBytes c a)

/-- A conditional output requirement, not a count bound on the entry domain.
    Dead, NULL, miss and rejected-saturation inputs need no output storage. -/
def LookupOutputNeeded (v : LookupRelation.View) : Prop :=
  ∃ n, v.count = some n ∧ n ≠ 0 ∧ n+1 < 2^31

def LookupOutputWrites (v : LookupRelation.View) (s : MachineState) (a : BitVec 64) : Prop :=
  LookupOutputNeeded v ∧ InRange s.data.regs.rcx.toBitVec 8 a

def LookupPendingRead (preempt : BitVec 32) : Prop := (preempt+1) &&& 0x00ffff00 = 0

/-- Named physical entry obligations. Separation is an explicit allocation
    discipline, not a claim that every safe x86 alias is admitted. No live-
    peer or positive-count invariant is imposed. Every byte range belongs
    to lookup, its helper, its stack or its named service callbacks. -/
structure LookupEntry (c : LookupRelation.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (returnAddress : UInt64) (s : MachineState)
    (world : Leanux.World) (v : LookupRelation.View) : Prop where
  pc : s.pc = Image.Lookup.entry
  frame : EntryFrame s returnAddress
  table : s.data.regs.rdi.toBitVec = c.table
  query : (s.data.regs.get (.low .rdx .W32)).toNat = c.query
  kinds : KindMask (s.data.regs.get (.low .rsi .W32)) c.kinds
  projected : LookupRelation.project c world = some v
  focus : LookupRelation.EntryFocus c v
  physical : LookupRelation.Physical c [s] [LookupObservation.call "wg_index_hashtable_lookup" s] s v
  steps : world.steps.toList = c.incomingSteps
  rxSection : world.netRxSection = c.rxSection
  coverageAt : LookupCoverageAt coverage preempt v s.data.dmem
  preemptAt : load32 s.data.dmem preemptCountAddress = some preempt
  stackMapped : ∀ n < LookupStackWords c,
    (s.data.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true
  outputMapped : LookupOutputNeeded v → (s.data.dmem.loadInt s.data.regs.rcx.toBitVec 8).isSome = true
  bhHardirq : (512+preempt) &&& 0x000f0000 = 0
  bhPending : LookupPendingRead preempt → s.data.dmem.loadInt softirqPendingAddress 2 = some 0
  readsScratch : ∀ a, LookupRelation.Reads c v a →
    ¬(LookupStackWrites c s a ∨ LookupCoverageWrites coverage preempt v a ∨ InRange preemptCountAddress 4 a)
  serviceStack : ∀ a, LookupServiceBytes coverage preempt v a → ¬LookupStackWrites c s a
  coverageStack : ∀ a, LookupCoverageWrites coverage preempt v a → ¬LookupLiveStack c s a
  coverageMetadata : ∀ a, LookupCoverageWrites coverage preempt v a → ¬LookupMetadataBytes coverage preempt v a
  coveragePreempt : ∀ a, LookupCoverageWrites coverage preempt v a → ¬InRange preemptCountAddress 4 a
  bhStack : ∀ a, InRange preemptCountAddress 4 a → ¬LookupLiveStack c s a
  bhMetadata : ∀ a,
    (LookupMetadataBytes coverage preempt v a ∨
      (LookupBufferNeeded coverage preempt v ∧ KcovStorageBytes coverage a)) →
    ¬InRange preemptCountAddress 4 a
  dataService : ∀ a, LookupServiceBytes coverage preempt v a → ¬LookupDataWrites c v a
  dataReturn : ∀ a, InRange s.data.regs.rsp.toBitVec 8 a → ¬LookupDataWrites c v a
  dataBucket : ∀ a, LookupBucketBytes c v a → ¬LookupDataWrites c v a
  ownerCount : ∀ a, LookupCountBytes c a → ¬LookupOwnerBytes c a
  outputProtected : ∀ a, LookupOutputWrites v s a →
    ¬(LookupRelation.Reads c v a ∨ LookupServiceBytes coverage preempt v a ∨
      InRange (s.data.regs.rsp.toBitVec-48) 56 a ∨ LookupCoverageWrites coverage preempt v a)
  pendingFrame : LookupPendingRead preempt → ∀ a, InRange softirqPendingAddress 2 a →
    ¬(LookupStackWrites c s a ∨ LookupCoverageWrites coverage preempt v a ∨
      LookupDataWrites c v a ∨ LookupOutputWrites v s a)

/-- Entry domain relative to the supplied source World and fixed ABI/address
    interpretation. Its machine-side domain existentially closes world and
    these interpretation parameters. No execution or R-preservation premise
    occurs here; LookupWitness supplies a concrete inhabitant and its test
    executes that exact state to the recorded return. -/
def Pre_lookup (c : LookupRelation.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (returnAddress : UInt64) (s : MachineState) (world : Leanux.World) : Prop :=
  ∃ v, LookupEntry c coverage preempt returnAddress s world v

end Binary.TrustBase
```


### Conditional callback core and helper framing

The conditional callback core now derives readiness from the witnessed
entry domain, rather than assuming the old uniform metadata invariant.
`LookupCoverage.Context` fixes the entry view and both preempt contexts;
its current physical count changes independently. PC eligibility covers
both contexts. Comparison eligibility requires the actual nonempty bucket
and post-BH context, and is not a field of general callback readiness.
Disabled callbacks leave memory exactly unchanged. Enabled callbacks use
the existing bounded buffer arithmetic and produce the conditional write
footprint named in Pre. No field was added to Pre, R or the trust surface.

`KcovInvariant.plan_normal_form_of_reads` factors the existing arithmetic;
the old stronger theorem is a wrapper. `LookupCoverage` proves conditional
readiness, caller-store framing and callback preservation;
`LookupCoverageCalls.callback` applies the same named service contract and
retains NoAnchoredReentry. `LookupPeerRelation.Physical.frame_count` and
`R.advance_count` preserve the bucket and owner words while requiring the
count equation to be proved from the executed pending-increment phase.
They do not claim that an arbitrary permitted count write preserves R.

The 291-job capped default build passed with standard-only axioms for these
new declarations. Fresh kernel replays passed for LookupCoverageCalls and
LookupPeerRelation with their imports; the changed-path escape scan and
diff check passed. Earlier attempts failed on a heartbeat limit, a command
syntax error, and two guard simplification proofs; those failed attempts
are not accepted results. A final nonoverlapping build confirmed the green
result after two earlier build processes briefly overlapped. The callback
core now elaborates in seconds; the shared arithmetic refactor takes about
41 seconds. No new KILLED banner occurred at this checkpoint.

This closes supporting callback obligations, not the 36-module execution
history plumbing or the complete helper/function simulation. In particular,
NoAnchoredReentry must remain available through callback histories: no-cuts
alone is insufficient, since the count scanner's CMPXCHG trigger is not a
correspondence cut. The actual lookup-to-helper call returns to +0xba and
must be composed in the outer lookup history. No certified function or
transported property is added; the current TrustBase quoted above is
unchanged.

Measured follow-on interval: 06:48:56 to 07:03:24 UTC, 868 seconds. It adds
conditional callback proofs and a helper relation-frame lemma, with zero
new certified anchored regions/functions (zero per agent-day). These proofs
were hand-finished; the implementation is not an automated grind-rate result.


### Main refresh and history wrappers, 07:10 UTC

[USER 2026-10-15] Merge the representation batch at cb2348e at a natural
point. It was merged into task/binary-tv as 61ce4a1; main was not advanced.
The charter now carries the minimal WireGuard frame wording. No binary
lookup proof repair was needed for the queue/runner representation changes;
no claim is made about campaign 1's separate lagging results.

The default binary build passed after the merge (291 jobs), then passed
with the conditional callback-history wrappers (294 jobs). The recorded
same-bucket miss three-way comparison and exact 191-instruction witness
both passed against the merged mirror. Fresh kernel replays passed for
LookupWitness and LookupCallPhase with their imports; their printed axioms
remain standard only. No KILLED banner or timeout occurred in these checks.

`LookupCoverageHistory` and `LookupCallHistory` retain the existing named
service contract's NoAnchoredReentry in the actual appended service
history, alongside its return and observations. `LookupCallPhase` proves
phase preservation from that fact and explicit exclusion of the two phase
trigger PCs. No-cut evidence alone is not used to justify it. The next
integration step is to replace the old stronger callback invariant through
the bucket and helper histories, deriving comparison eligibility at the
actual nonempty-bucket branch. The helper's CMPXCHG/cut composition,
function theorem and transport remain open. TrustBase and its quoted text
above are unchanged; certified-function throughput remains zero.


### Entry through the bucket loop, 07:34:38 UTC

The execution histories now use the conditional callback invariant from the
witnessed entry domain. Comparisons require a nonempty selected bucket at
the actual comparison path; empty-bucket and NULL-helper paths introduce no
such requirement. Zero-count peers remain admitted. No change was made to
Pre_lookup, R or TrustBase, whose verbatim text above still matches the file.

`LookupFromPre.bucket_from_pre` composes the actual prologue, BH-disable and
complete bucket search directly from Pre_lookup, retaining all-cut R and
matching against LookupSearch.result. Header phase, ABI registers, callback
readiness and memory separation are derived rather than added as headline
premises. Its retained loop-head history is explicitly a prefix of the
final history, addressing a read-only review's interface finding.

The default capped build passed (295 jobs); the final review amendment's
target build passed (97 jobs). Fresh kernel replays passed for LookupFromPre
and the live, dead and NULL helper histories, including their imports;
LookupFromPre was replayed again after the prefix amendment. Printed axioms
are only propext, Classical.choice and Quot.sound. The changed-path escape
scan and diff check passed. A first replay invocation incorrectly supplied
multiple modules with --fresh and failed; each was subsequently replayed
with the supported single-module invocation. Ordinary elaboration errors
in the bridge were fixed. No KILLED banner or timeout occurred here.

Two read-only reviews found no domain regression or lost observations in
the callback refactor or entry composition. The missing loop-head prefix
fact was fixed. The stronger per-cut byte frames remain available in the
underlying segment lemmas; their eventual function-level frame composition
is still work to do, not an asserted consequence of this wrapper.

Measured interval: 07:10:46 to 07:34:38 UTC, 1432 seconds. This integrates
35 history modules and adds the entry-to-bucket composition; it does not
certify a new anchored function or add new separately certified regions.
Certified-function throughput is still zero. The changes were hand-finished
with scripted mechanical renaming, not an automated region-grind result.
The complete peer-get all-cut relation, owner/BH/return composition, generic
frame transport and function-level lookup theorem remain open. In particular,
ScanFrame still discards callback no-reentry evidence; preserving the count
scanner through the same executed prefixes is the next integration step.


### Actual count phase through every helper path, 08:14:39 UTC

The lookup prefix and bucket loop now retain scanner stability through their
actual instruction histories. Service calls use the named contracts' retained
NoAnchoredReentry evidence; absence of cuts alone is not substituted for it.
The live helper retains the exact +0x44 history prefix shared by its count
phase and old/new memory-frame partition. The NULL and zero-count helper
paths retain scanner preservation through the final RET. No change was made
to R, Pre_lookup, TrustBase, the mirror, or Kraken at this checkpoint.

`PeerCountCuts` proves the count equation at every appended correspondence
cut. Before CMPXCHG it is the ordinary old word; afterward it is the captured
old operand with the physically incremented word; at RET it is the committed
successor. The two raw successors before the store are proved not to be cuts.
The count bound is a local arithmetic premise supplied by accepted source
execution, not a new entry-domain restriction. `LookupHelperPhase` derives
the activity guard from the actual observed prefixes. Its nonempty scanner
seed is only a proof device for excluding earlier RET observations. It is
propagated from the singleton lookup entry; these APIs are local to this
anchored invocation, not histories containing an earlier completed helper.

`LookupPeerSource` proves the exact returned source projection and preserves
the embedded owner word even when the owner is the incremented peer.
`LookupPeerRelation` supports committing that count using the executed write
frame. `CorrespondencePrefix` restricts point matching to actual raw prefixes
without changing the emitting occurrence, then composes it with proved
cut-state relations. `PeerReturnObservation.helper_return_prefix` identifies
the exact decision-only observation prefix before the final helper RET.
These are supporting lemmas: the complete helper R theorem still needs their
composition with its concrete source decision worlds and physical frames.

Read-only review found the phase witness was initially separate from the
physical old/new boundary. The remedy binds them to the same history prefix;
the exact-boundary schedule and cut theorem were reviewed afterward. A second
review found no incorrect phase/prefix guarantee or owner-word regression.
It emphasized that prefix composition does not itself prove the cut-state R
facts and that arbitrary return destinations still need the endpoint proof.

The capped default build passed (303 jobs). Fresh kernel replays passed for
LookupFromPre, PeerLiveEntryHistory, PeerDeadEntryHistory,
PeerNullEntryHistory, LookupHelperPhase and LookupPeerSource, each including
its imports. The final return-prefix amendment was rebuilt and LookupHelperPhase
was replayed again. Printed axioms are standard only; the changed-path escape
scan and diff check passed. Ordinary elaboration failures during development
were fixed; no KILLED banner or timeout occurred. Reproduce with `capped --
lake build` in binary/, then `capped -- lake env leanchecker --fresh MODULE`
for each of the six modules above. The previously recorded three-way/witness
runs remain the latest runtime checks; this checkpoint changes proofs only.

Measured interval: 07:34:38 to 08:14:39 UTC, 2401 seconds. It adds phase
composition and count equations, not a newly certified anchored region or
function: zero new certified regions/functions, zero per agent-day. The
proofs were hand-finished with mechanical scripted edits; no automated grind
throughput is claimed. The complete helper simulation, owner/BH/return
composition, generic untouched-WireGuard frame transport and function-level
lookup theorem remain open. No landed property is yet transported. The
verbatim TrustBase quoted above remains byte-for-byte current.

### Helper simulation and accepted source bridge, 09:35:24 UTC

Milestone 1 is still incomplete. `LookupHelperPrepared.helper_from_call`
now executes every accepted helper path (NULL, present zero-count, and live)
from the actual lookup CALL to the actual return at lookup+0xba. It retains
R at all emitting points and all anchored cuts, the exact helper-return
snapshot, the conditional write footprint, and the logged source execution
for every incoming source history. Its ABI, mapped stack and separation
premises are derived from LookupEntry and the executed bucket/call prefix.
`LookupAcceptedSource.lookup_accepts_helper` derives helper acceptance from
the actual accepted indexLookup run and retains that run's accepted suffix.
These are supporting compositions, not the section 1 function theorem.

[AGENT 2026-10-15] Add four semantic successors to the correspondence cuts:
peer-get +0x96, +0xb7, +0xc8 and +0xd6. They emit the source's computed
live/dead, negative and wrap decisions even without a corresponding branch.
The generator derives the successors from the decoded instruction lengths
and checks instruction boundaries; the observer checks the exact successor.
The decoded instruction listing and fetch function are unchanged. This adds
no service premise: NoAnchoredReentry already excludes every anchored
instruction address, not merely listed cuts.

The physical owner-store component now relates the pending word to the
actual helper-return snapshot, and its committed word to the actual returned
value, including NULL. `LookupOwnerSource.owner_set_project` proves the
landed setter preserves the focused count even when the handshake owner is
the referenced peer. Finding 1 remains recorded. Neither Pre_lookup nor R
was narrowed, and TrustBase is unchanged; its verbatim quotation above is
still byte-for-byte current. No ISA extension was needed in this interval.

Read-only review identified and repaired three API omissions: four missing
semantic cuts, failure to retain the exact helper-return machine, and an
unconditional count-write separation premise on the dead branch. The
accepted helper now requires count-write separation only on the live branch
and retains that conditional footprint. Another review requested the logged
helper equation for arbitrary incoming histories; that is now exported.
No soundness defect or additional dead-peer restriction was found in the
entry-to-helper composition. A further valid alias case remains to carry:
the output may overlap dead helper scratch below the outer saved frame.
The broad byte frame alone does not prove that this storage remains mapped;
the executed return has the necessary facts. They will be retained, without
strengthening Pre_lookup. This is a proof-interface omission, not a mirror
or kernel defect.

Validation: the default capped build passed (324 jobs). Fresh kernel replay
passed LookupHelperPrepared, LookupOwnerSource and LookupOwnerRelation,
and LookupAcceptedSource, including their imports. Printed axioms are standard only. The changed-code escape
scan and diff check passed, and the TrustBase quote comparison passed. The
three-way test was rerun after the observer/cut change on
`d1_wrong_receiver_index_same_bucket`, with exact per-invocation coverage,
repetitions, helper coverage and operands, and mirror decisions agreeing.
The exact Pre witness ran to return: 191 instructions, six points, two
undefined-value seeds. It is materialised from the recorded operation's
mirror read projection, not a captured kernel entry or a reachability proof.
Reproduce with `LEANUX_QEMU_SLOTS=16 capped -- /usr/bin/python3 -B binary/run.py
--check .artifacts/check/binary-tv-20261015-024459 --trace
d1_wrong_receiver_index_same_bucket`, and in binary/ with
`LEANUX_QEMU_SLOTS=16 capped -- lake env lean LookupWitnessTest.lean`.

Development failures were not passes: ordinary elaboration failures, one
Lean deterministic heartbeat timeout in an intermediate returning-interior
proof, an initial generator invocation using an interpreter without
pyelftools, and an escape-scan false positive caused by stripping line
comments before block comments. The proof was restructured without the
attempted recursion override; generation succeeded with /usr/bin/python3;
the corrected code-only scan passed. No KILLED banner or wall timeout
occurred. No native reduction axiom or proof escape was introduced.

Measured interval: 08:14:39 to 09:35:24 UTC, 4845 seconds (1.346 primary-agent
hours), with two concurrent read-only reviews. Three helper path compositions,
entry/call preparation and source acceptance were hand-finished; they are
not counted as separately certified anchored regions. Zero newly certified
regions/functions, hence zero certified regions/functions per agent-day;
no automated grind throughput or property transport is claimed. The owner
region's complete cut composition, output mapping/store, BH-enable and outer
return, generic untouched-WireGuard frame transport, and the function-level
lookup theorem remain open. This is a progress checkpoint, not the
milestone-1 go/no-go report.


## Milestone 1: function theorem and review handoff

[AGENT 2026-10-15] **GO to the independent surface review.** The direct
region method has closed lookup from its witnessed entry to its original
caller, with the bucket loop and every accepted helper outcome. Scaling
beyond this function waits for that review, as the charter requires. There
is no measured automated grind rate on which to forecast the remaining
campaign.

`Binary.LookupRelation.lookup_simulation` in `LookupAdequacy.lean` proves
Kraken `Eventually` execution from the actual entry under `Pre_lookup`, the
anchored decoder agreement and five named service contracts, conditional
on acceptance of the executable `indexLookup` run. It returns through the
original ABI frame, proves NULL versus the selected entry in RAX and the
live peer output word, and realizes the exact accepted source history.
Every emitted point and every anchored cut uses its actual instruction
prefix and the corresponding source World. The postcondition carries both
endpoint R and physical equality outside the lookup footprint, including
that frame at every anchored cut. Undefined instruction outcomes remain
universally quantified by the step semantics.

The composed execution includes arbitrary bucket collisions, empty or
exhausted buckets, first-match wrong-kind stops, NULL owner words, zero
reference counts, and accepted live increments. Source-refused refcount
outcomes remain outside the acceptance premise, as section 1 requires.
No region preservation, future readiness, expected decision sequence or
positive-peer invariant is an execution premise. `Pre_lookup`, its named
`LookupEntry` clauses, `R`, and `TrustBase.lean` are unchanged from
checkpoint `8aab779`. Finding 1 remains recorded above; the executed dead
region stores NULL through the embedded owner, so the fixed mirror and
binary agree on the two-lookup witness. This work does not establish
reachability of an entry during a zero-to-RCU-release interval or settle
that broader lifecycle claim.

`lookup_transport` carries arbitrary predicates on the same accepted run
through minimal R. An internal review correctly rejected treating omitted
World fields as already physically represented. That finding is fixed by
retaining the regions' physical cut frames and by
`lookup_framed_transport`: an initial interpretation, a byte-footprint frame
rule and a proved source observer invariant carry the interpretation to the
same run's exact cut prefixes and final World. These are explicit frame-rule
premises, not hidden additions to the lookup execution domain. Service
interiors are not claimed to preserve every byte; their contracts exclude
anchored reentry and specify their return effects.

The concrete source theorem `LookupSourceFrame.lookup_receivingSnapshot`
keeps the keypair allocation frontier, existence at every source ID,
lifetime stamp, receive counter and entire bitmap equal at every logged
point and return. `lookup_snapshot_transport` is one application of the
generic frame rule with the DWARF-derived physical field interpretation.
It preserves the frontier and source-live stamp/counter/bitmap bytes,
conditional on initial interpretation and disjointness from the proved
writes. It does **not** determine physical allocator membership/absence;
the existing Pre witness does not witness these extra frame-instance
premises. Thus the lookup frames needed by replay-window/lifetime results
are available. Whole-trace S1–S3, R1–R6 and H1–H6 are not certified by this
one function: their remaining anchors and the milestone-4 entry-realism
check are still required. The mirror proof register's existing lag is
unchanged.

The handwritten composition closes 54 decoded region identities: 23 lookup
and 31 peer-get. Their instruction facts comprise 37 proof schemas: 15
lookup regions plus one shared CALL proof for eight sites; 20 peer-get
regions plus one shared CALL proof for eleven sites. Generation supplies
literal instruction terms, DWARF offsets and layout equalities. All symbolic
execution, invariants and composition were hand-finished with Lean tactics;
no end-to-end automatic region prover or certificate checker was built.
The single accepted-nonnull helper theorem covers both dead and live
results, with NULL covered by its companion theorem and composed into the
lookup theorem.

**Measured rate.** From the charter checkpoint `36cfe55` at
2026-10-14 17:56:58 UTC to the report cutoff 2026-10-15 10:55:34 UTC:
61,116 elapsed seconds (16.977 hours), one lookup function and its
helper, 54 region identities. That is 3.181 region identities per
elapsed hour, or 76.34 per 24-hour **elapsed primary-agent day**;
lookup throughput is 1.414 functions per such day. This denominator
includes pauses, setup, discarded out-of-scope relation work and review.
It is an elapsed-throughput proxy, **not aggregate agent labor**: concurrent
subagent duration was not metered consistently, so an honest aggregate
regions-per-agent-day figure is unavailable. Automated complete region
certifications: zero; hand-finished identities: 54. The current composition
interval, 09:35:24–10:55:34 UTC (4,810 seconds), inherited the instruction
facts; dividing all 54 by that interval would inflate the rate. Future
milestones need explicit aggregate-agent time accounting for a comparable
labor rate. [AGENT] Use this first milestone as evidence of feasibility,
not an automatic-throughput estimate.

The mirror pin is `cb2348e`, already merged here as `61ce4a1`. WG/FS/Kernel
sources remain byte-identical to main. Kraken remains on the private
`task/binary-adequacy` branch at
`e033e3dac812a576881a329b2d4c174364f3d44c` (upstream `8af7806`). The campaign's
ISA additions are memory CMPXCHG, JS and index-only address parsing, with
the tests and manual comparison recorded above and the reconstructible
patches in `binary/kraken-patches/`. No ISA addition or trust-base addition
was needed in this final composition interval. The service contracts are
`TracePcContract`, `TraceCmp4Contract`, `TraceConstCmp4Contract`,
`TraceConstCmp1Contract` and `BhEnableContract`; they remain hypotheses,
not proved implementations. The literal ELF/decoder/hardware interpretation
remains external as the trust file states.

Validation, all heavy commands capped and concrete runs using
`LEANUX_QEMU_SLOTS=16`:

- Default binary build: PASS, 351 jobs.
- `scripts/proof-gate --binary`: PASS, nine headline/witness/frame/composition
  declarations; only `propext`, `Classical.choice`, `Quot.sound`, with no
  axioms for `compose_regions`. Proof-source escape scan passed.
- Fresh kernel replay: PASS separately for `LookupSnapshotTransport` and
  `LookupWitness`, including their import closures.
- `lake check --inadvisably-no-sandbox`: PASS; Lean's default kernel accepted
  the exported solution with the same three standard axioms. This is the
  box-rule **speedbump**, not the outside-Nono sandboxed claim gate.
- Exact `LookupWitness.witness_pre` state: PASS to return, 191 instructions,
  six observed points, two undefined-value seeds. This state is materialized
  from the recorded operation's mirror read projection; it is not a captured
  kernel entry or a reachability proof.
- Three-way test on `d1_wrong_receiver_index_same_bucket`: PASS, exact
  per-invocation coverage including repetitions and decoded peer-get,
  comparison operands and mirror decisions. Memory is compared with the
  mirror, not with unrecorded kernel memory.
- Unit tier after `capped -- lake build leanux-model`: PASS, 126 tests, one
  skip (22.960 seconds). The stale-executable failure is recorded below.
- Diff check and unchanged Pre/R/trust-file checks: PASS.

Reproduction commands are in `binary/README.md`. The three-way recording
can be regenerated with `binary/run.py --trace
 d1_wrong_receiver_index_same_bucket`; `--check
 .artifacts/check/binary-tv-20261015-024459` reuses the existing disposable
recording. [AGENT] The charter-prescribed binary proof gate is implemented
as `scripts/proof-gate --binary` and documented in the working-practices
file; the mirror acceptance gate is unchanged.

Failures were not counted as passes: development elaboration failures,
one deterministic Lean recursion-depth failure (the oversized expression
was removed), an invalid multi-module `leanchecker --fresh` invocation
(corrected to separate modules), and a helper replay during a concurrent
dependency rebuild (superseded by the successful final closure replay).
The unit tier first failed the new batch-completion test because the mirror
executable was stale after the main merge; it was rebuilt before one rerun.
No KILLED banner or wall timeout occurred in this final interval. I also
mistakenly delegated disjoint file edits concurrently despite the charter's
one-writer rule; this was stopped, agents returned to read-only review, and
all subsequent edits were applied by the primary writer. No other worktree,
main, shared dependency source, or global configuration was changed.

Internal read-only review's frame finding is fixed. Its physical membership
and witness-scope cautions are accepted and explicit above. This is not the
coordinator's no-context surface review and does not replace it. Before
milestone 2, the coordinator should send the headline statement, transport,
`compose_regions`, Pre, the witness and the trust file to that reviewer.
The supplied AGENTS.md also requires the user to run `capped -- lake check`
from this worktree's `binary/` outside Nono at the claim point. That external
gate remains pending. No merge to main and no push were performed.

### External gate for the reviewed milestone-1 checkpoint

[USER 2026-10-15] The user ran the external gate outside Nono from
`binary/` at commit `430ea90`:

```sh
lake check --from-export ../.tmp/binary-m1.ndjson
```

The leanexport contains `LookupAdequacy`, `LookupSnapshotTransport`,
`LookupWitness`, `TrustBase` and `Execution`. The reported output was:

```text
Lean default kernel accepts the solution; uses axioms: propext, Quot.sound, Classical.choice
```

This satisfies the external toolchain gate for **430ea90** and supersedes
that checkpoint's pending-gate status above. It does not validate subsequent
review fixes. The export is disposable (about 1.1 GB), not a committed
artifact. Export-based checking is needed because sandboxed `lake check`
cannot see this package's path dependencies.

### TrustBase.lean, verbatim at the milestone-1 handoff

```lean
import History
import Image
import ServiceImage
import Memory
import LookupProjection

/-! Named trust surface for the pinned lookup proof, under construction.
    These are explicit hypotheses, not globally asserted facts. No declaration
    here assumes the lookup result, a region's R-preservation, or a mirror run.
    Pre_lookup is accompanied by its concrete satisfying witness.
    The final milestone report must reproduce this file verbatim.

    External interpretation: binutils 2.42 supplied the literal AST and DWARF
    layouts from the ELF below. Lean checks execution of those terms, not the
    binutils decoder, DWARF producer, SHA computation or correspondence of
    Kraken's model with x86 hardware. The loader checks identity and branch
    encodings. Mutable runtime globals are NOT assumed equal to ELF initial
    bytes at a function entry; their current values belong in Pre_lookup.
-/
namespace Binary.TrustBase

def krakenCommit : String := "e033e3dac812a576881a329b2d4c174364f3d44c"
def kernelIdentity : String := "6b2018b9"
def elfSha256 : String := "16c346209885db6c610d4aa126c6eb30f5d3c02f0498d95e606473945f648774"
def decoderVersion : String := "GNU objdump (GNU Binutils for Ubuntu) 2.42"

local instance : Labels := Image.linkedLabels

/-- The partial linked decoder for both anchored functions and all reached
    service bodies. A rejected instruction remains a failing fetch; neither
    its semantics nor successful execution is assumed by this definition. -/
def pinnedFetch (pc : Int64) : Option Decoded :=
  (Image.fetch pc).orElse (fun _ => ServiceImage.fetch pc)

/-- The ambient instruction image is this fixed ELF-derived listing,
    including service bytes. This is the external bytes-to-AST assumption. -/
def WholeImageDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  fetch = pinnedFetch

/-- The ambient decoder agrees with the pinned literal instructions/lengths.
    Interpreting those literals as this ELF is the external decoding assumption. -/
def AnchoredDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, Image.fetch pc = some instruction → fetch pc = some instruction

/-- No alternatives/static-key text change in a certified anchored range. -/
def AnchoredTextStable (fetchAt : Nat → Int64 → Option Decoded) : Prop :=
  ∀ time pc instruction, Image.fetch pc = some instruction → fetchAt time pc = some instruction

/-- Read-only image bytes remain the linked bytes. `linked` is the loader's
    fixed ELF projection; it is not chosen independently at each proof point. -/
def ReadOnlyImage (linked : Mem 64) (readOnly : BitVec 64 → Prop) (memory : Mem 64) : Prop :=
  ∀ address, readOnly address → memory.get? address = linked.get? address

/-- External paging/access permissions, absent from Kraken MachineState. -/
structure Permissions where
  read : BitVec 64 → Width → Prop
  write : BitVec 64 → Width → Prop
  execute : Std.Rco Int64 → Prop

/-- Kraken's All grants permission requests. This separate premise makes
    that grant explicit for every effect, including every undefined outcome. -/
def AccessAllowed (permissions : Permissions) : Effects → Prop
  | .done _ => True
  | .unimplemented _ | .gp_unaligned .. | .nonmem_load .. | .nonmem_store .. => False
  | @Effects.undefined α _ next => ∀ value : α, AccessAllowed permissions (next value)
  | .require_read_access address width next =>
      permissions.read address width ∧ AccessAllowed permissions (next ())
  | .require_write_access address width next =>
      permissions.write address width ∧ AccessAllowed permissions (next ())
  | .require_exec_access pc next =>
      permissions.execute pc ∧ AccessAllowed permissions (next ())

/-- Every actually executed instruction has its requested accesses granted;
    the final return destination is not itself executed by this run. -/
def RunAccessAllowed (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (history : List MachineState) : Prop :=
  ∀ s ∈ history.dropLast, ∃ decoded, fetch s.pc = some decoded ∧
    permissions.execute ⟨s.pc, s.pc + .ofNat decoded.size⟩ ∧
    AccessAllowed permissions
      (decoded.instruction.interp s.data ⟨s.pc, s.pc + .ofNat decoded.size⟩
        (fun d => .done ⟨d, s.pc + .ofNat decoded.size⟩) (fun pc d => .done ⟨d, pc⟩))

/-- The environment places no interrupt, preemption or competing CPU action
    inside this anchored call; the records place such actions between calls. -/
structure SerializedEnvironment (onlineCPUs : Nat) (externalActions : List Nat) : Prop where
  singleCPU : onlineCPUs = 1
  noInterleaving : externalActions = []

/-- Kernel ABI: the stack word is the actual CALL return address. Eight-byte
    alignment follows this kernel's compiler flags, not a userspace ABI guess. -/
def EntryFrame (s : MachineState) (returnAddress : UInt64) : Prop :=
  s.data.regs.rsp.toNat % 8 = 0 ∧
  s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8 = some (returnAddress.toNat : Int)

/-- Only ABI-preserved registers are constrained; caller-save registers and
    flags may change. The callee has consumed the actual return-address word. -/
def Returned (entry final : MachineState) (returnAddress : UInt64) : Prop :=
  final.pc = .ofBitVec returnAddress.toBitVec ∧
  final.data.regs.rsp = entry.data.regs.rsp + 8 ∧
  final.data.regs.rbx = entry.data.regs.rbx ∧
  final.data.regs.rbp = entry.data.regs.rbp ∧
  final.data.regs.r12 = entry.data.regs.r12 ∧
  final.data.regs.r13 = entry.data.regs.r13 ∧
  final.data.regs.r14 = entry.data.regs.r14 ∧
  final.data.regs.r15 = entry.data.regs.r15

/-- Service internals emit no anchored observation or cut. The final state
    may return to an anchored address; it is deliberately not excluded. -/
def NoAnchoredReentry (history : List MachineState) : Prop :=
  ∀ s ∈ history.dropLast, Image.fetch s.pc = none

/-- A service contract uses the same fetched-instruction execution as the
    function proof. Its readiness and write footprint are physical predicates;
    their concrete instantiations must be part of the witnessed entry domain. -/
def ServiceReturns (fetch : Int64 → Option Decoded) (address : Int64)
    (ready : MachineState → Prop) (writes : MachineState → BitVec 64 → Prop)
    (effect : MachineState → MachineState → Prop) : Prop :=
  ∀ s returnAddress, s.pc = address → ready s → EntryFrame s returnAddress →
    Eventually (historyStep fetch)
      (fun t => Returned s t.machine returnAddress ∧
        EqualOutside (writes s) s.data.dmem t.machine.data.dmem ∧
        effect s t.machine ∧ NoAnchoredReentry t.history)
      ⟨s, [s]⟩

def preemptCountAddress : BitVec 64 := .ofNat 64 0xffffffff81cc85c8
def currentTaskAddress : BitVec 64 := .ofNat 64 0xffffffff81cc85c0
def softirqPendingAddress : BitVec 64 := .ofNat 64 0xffffffff81cc85e0

inductive KcovKind where
  | pc | cmp4 | constCmp4 | constCmp1
  deriving DecidableEq

structure WordWrite where
  address : BitVec 64
  value : BitVec 64

def load64 (memory : Mem 64) (address : BitVec 64) : Option (BitVec 64) :=
  (memory.loadInt address 8).map (.ofInt 64)

def load32 (memory : Mem 64) (address : BitVec 64) : Option (BitVec 32) :=
  (memory.loadInt address 4).map (.ofInt 32)

/-- Physical callback metadata, fixed during an anchored call except for the
    separately balanced preempt count. Capacity is a count of 64-bit words. -/
structure KcovLayout where
  task : BitVec 64
  area : BitVec 64
  capacity : BitVec 32
  mode : BitVec 32
  softirqEnabled : BitVec 32

/-- Exact runtime metadata reads, not the ELF's initial global bytes. -/
def KcovMetadata (layout : KcovLayout) (memory : Mem 64) : Prop :=
  load64 memory currentTaskAddress = some layout.task ∧
  load32 memory (layout.task + 0x6e0) = some layout.mode ∧
  load32 memory (layout.task + 0x6e4) = some layout.capacity ∧
  load64 memory (layout.task + 0x6e8) = some layout.area ∧
  load32 memory (layout.task + 0x704) = some layout.softirqEnabled

/-- Mapped buffer and bounded runtime header. A full buffer is allowed; no
    callback is required to have room for a record. This predicate says
    nothing about the peer state or the lookup result. -/
def KcovBuffer (layout : KcovLayout) (memory : Mem 64) : Prop :=
  (∀ word < layout.capacity.toNat,
    (memory.loadInt (layout.area + .ofNat 64 (8 * word)) 8).isSome = true) ∧
  ∃ count : Nat, count ≤ layout.capacity.toNat ∧
    load64 memory layout.area = some (.ofNat 64 count)

def KcovBufferBytes (layout : KcovLayout) : BitVec 64 → Prop :=
  InRange layout.area (8 * layout.capacity.toNat)

/-- Storage read by an active callback. Even capacity zero still requires
    the header; caller writes must preserve it as well as the buffer words. -/
def KcovStorageBytes (layout : KcovLayout) (address : BitVec 64) : Prop :=
  InRange layout.area 8 address ∨ KcovBufferBytes layout address

def KcovMetadataBytes (layout : KcovLayout) (address : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 address ∨
  InRange (layout.task + 0x6e0) 4 address ∨
  InRange (layout.task + 0x6e4) 4 address ∨
  InRange (layout.task + 0x6e8) 8 address ∨
  InRange (layout.task + 0x704) 4 address

/-- Physical disjointness from protected memory (metadata, live stack and
    represented objects). Readiness is proved from this, not assumed at
    every callback. The caller chooses the actual protected footprint. -/
def KcovSeparated (layout : KcovLayout) (protectedBytes : BitVec 64 → Prop) : Prop :=
  ∀ address, KcovBufferBytes layout address → ¬protectedBytes address

/-- Physical state carried between callbacks. Disabled tracing requires no
    mapped coverage area; the mode field itself still belongs to the task. -/
def KcovState (layout : KcovLayout) (preempt : BitVec 32) (memory : Mem 64) : Prop :=
  KcovMetadata layout memory ∧
  load32 memory preemptCountAddress = some preempt ∧
  (layout.mode = 2 ∨ layout.mode = 3 → KcovBuffer layout memory)

/-- Bytes that caller stores must preserve. Buffer storage is needed only
    in an active mode; metadata and preemption state are always physical. -/
def KcovStateBytes (layout : KcovLayout) (address : BitVec 64) : Prop :=
  KcovMetadataBytes layout address ∨ InRange preemptCountAddress 4 address ∨
    ((layout.mode = 2 ∨ layout.mode = 3) ∧ KcovStorageBytes layout address)

/-- Physical KCOV callback specification, with the actual early-return read
    dependencies and machine-width arithmetic. It is not a proof checker. -/
def KcovPlan (kind : KcovKind) (s : MachineState) : Option (List WordWrite) := do
  let memory := s.data.dmem
  let preempt ← load32 memory preemptCountAddress
  let returnPC ← load64 memory s.data.regs.rsp.toBitVec
  let task ← load64 memory currentTaskAddress
  if preempt &&& 0xff0100 != 0 then
    if preempt &&& 0x100 == 0 || preempt &&& 0xff0000 != 0 then return []
    let softirqEnabled ← load32 memory (task + 0x704)
    if softirqEnabled == 0 then return []
  let mode ← load32 memory (task + 0x6e0)
  if mode != (if kind = .pc then 2 else 3) then return []
  let area ← load64 memory (task + 0x6e8)
  let capacity ← load32 memory (task + 0x6e4)
  let count ← load64 memory area
  if kind = .pc then
    let next := count + 1
    if next.toNat ≥ capacity.toNat then return []
    return [⟨area, next⟩, ⟨area + 8 * next, returnPC⟩]
  else
    let slot := 4 * count
    let ending := 8 * slot + 40
    if 8 * (capacity.setWidth 64) < ending then return []
    let tag : BitVec 64 := match kind with
      | .pc => 0
      | .cmp4 => 4
      | .constCmp4 => 5
      | .constCmp1 => 1
    let arg1 := if kind = .constCmp1 then (s.data.regs.get (.low .rdi .W8)).setWidth 64
      else (s.data.regs.get (.low .rdi .W32)).setWidth 64
    let arg2 := if kind = .constCmp1 then (s.data.regs.get (.low .rsi .W8)).setWidth 64
      else (s.data.regs.get (.low .rsi .W32)).setWidth 64
    return [⟨area, count + 1⟩, ⟨area + ending - 32, tag⟩,
      ⟨area + ending - 24, arg1⟩, ⟨area + ending - 16, arg2⟩,
      ⟨area + ending - 8, returnPC⟩]

/-- Planned destinations are mapped and do not overwrite the return word.
    Separation from all represented objects is an additional entry obligation. -/
def KcovReady (kind : KcovKind) (s : MachineState) : Prop :=
  ∃ stores, KcovPlan kind s = some stores ∧
    ∀ write ∈ stores,
      (s.data.dmem.loadInt write.address 8).isSome = true ∧
      ∀ address, InRange write.address 8 address → ¬InRange s.data.regs.rsp.toBitVec 8 address

def KcovWrites (kind : KcovKind) (s : MachineState) (address : BitVec 64) : Prop :=
  ∃ stores, KcovPlan kind s = some stores ∧
    ∃ write ∈ stores, InRange write.address 8 address

/-- Exact callback stores keep repeated-call buffer readiness provable;
    allowing arbitrary corruption of the coverage buffer would not suffice. -/
def KcovEffect (kind : KcovKind) (before after : MachineState) : Prop :=
  ∃ stores, KcovPlan kind before = some stores ∧
    after.data.dmem = stores.foldl
      (fun memory write => memory.storeInt write.address 8 write.value.toInt) before.data.dmem

/-- KCOV PC callback: only its physically planned stores may occur. -/
def TracePcContract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)

/-- KCOV variable/variable 32-bit comparison callback. -/
def TraceCmp4Contract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3e80) (KcovReady .cmp4) (KcovWrites .cmp4) (KcovEffect .cmp4)

/-- KCOV constant/variable 32-bit comparison callback. -/
def TraceConstCmp4Contract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3f00) (KcovReady .constCmp4)
    (KcovWrites .constCmp4) (KcovEffect .constCmp4)

/-- KCOV constant/variable 8-bit comparison callback used by peer-get. -/
def TraceConstCmp1Contract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3ec0) (KcovReady .constCmp1)
    (KcovWrites .constCmp1) (KcovEffect .constCmp1)

/-- The actual no-work BH-enable path, including nested disable counts.
    The softirq word is needed only on the branch that reads it. -/
def BhEnableReady (s : MachineState) : Prop :=
  ∃ count : BitVec 32,
    s.data.dmem.loadInt preemptCountAddress 4 = some (count.toNat : Int) ∧
    count &&& 0x000f0000 = 0 ∧
    ((count + 1 - s.data.regs.get (.low .rsi .W32)) &&& 0x00ffff00 = 0 →
      s.data.dmem.loadInt softirqPendingAddress 2 = some 0) ∧
    ∀ address, InRange preemptCountAddress 4 address → ¬InRange s.data.regs.rsp.toBitVec 8 address

/-- BH enable balances the actual low-32-bit count argument, modulo 2^32.
    Readiness must justify that its softirq path runs no pending work. -/
def BhEnableContract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810732c0) BhEnableReady
    (fun _ => InRange preemptCountAddress 4)
    (fun before after => ∀ old : BitVec 32,
      before.data.dmem.loadInt preemptCountAddress 4 = some (old.toNat : Int) →
      after.data.dmem.loadInt preemptCountAddress 4 =
        some ((old - before.data.regs.get (.low .rsi .W32)).toNat : Int))

/-- Whether the actual callback reads softirqEnabled before its mode test. -/
def LookupSoftRead (preempt : BitVec 32) : Prop :=
  preempt &&& 0xff0100 ≠ 0 ∧
  ¬(preempt &&& 0x100 = 0 ∨ preempt &&& 0xff0000 ≠ 0)

/-- The callback reaches its mode read only after the preemption/softirq gate. -/
def LookupModeRead (coverage : KcovLayout) (preempt : BitVec 32) : Prop :=
  if preempt &&& 0xff0100 ≠ 0 then
    ¬(preempt &&& 0x100 = 0 ∨ preempt &&& 0xff0000 ≠ 0) ∧ coverage.softirqEnabled ≠ 0
  else True

/-- PC callbacks occur before and after BH-disable. Comparisons occur only
    with a nonempty selected bucket, after the actual modular increment. -/
def LookupBufferNeeded (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) : Prop :=
  (coverage.mode = 2 ∧ (LookupModeRead coverage preempt ∨ LookupModeRead coverage (512+preempt))) ∨
  (coverage.mode = 3 ∧ v.bucket ≠ [] ∧ LookupModeRead coverage (512+preempt))

/-- Only callback metadata reached in one of this lookup's two contexts.
    Unused layout values impose no equality on memory. The active coverage
    allocation is mapped uniformly; a full buffer is permitted. -/
def LookupCoverageAt (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (memory : Mem 64) : Prop :=
  load64 memory currentTaskAddress = some coverage.task ∧
  ((LookupSoftRead preempt ∨ LookupSoftRead (512+preempt)) →
    load32 memory (coverage.task+0x704) = some coverage.softirqEnabled) ∧
  ((LookupModeRead coverage preempt ∨ LookupModeRead coverage (512+preempt)) →
    load32 memory (coverage.task+0x6e0) = some coverage.mode) ∧
  (LookupBufferNeeded coverage preempt v →
    load32 memory (coverage.task+0x6e4) = some coverage.capacity ∧
    load64 memory (coverage.task+0x6e8) = some coverage.area ∧ KcovBuffer coverage memory)

def LookupMetadataBytes (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 a ∨
  ((LookupSoftRead preempt ∨ LookupSoftRead (512+preempt)) ∧ InRange (coverage.task+0x704) 4 a) ∨
  ((LookupModeRead coverage preempt ∨ LookupModeRead coverage (512+preempt)) ∧ InRange (coverage.task+0x6e0) 4 a) ∨
  (LookupBufferNeeded coverage preempt v ∧
    (InRange (coverage.task+0x6e4) 4 a ∨ InRange (coverage.task+0x6e8) 8 a))

def LookupCoverageWrites (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  LookupBufferNeeded coverage preempt v ∧ KcovBufferBytes coverage a

def LookupServiceBytes (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  LookupMetadataBytes coverage preempt v a ∨ InRange preemptCountAddress 4 a ∨
  (LookupBufferNeeded coverage preempt v ∧ KcovStorageBytes coverage a)

/-- The helper is called for a selected owner even when its peer word is NULL. -/
def LookupStackWords (c : LookupRelation.Config) : Nat := if c.focus.owner.isSome then 13 else 6

def LookupStackWrites (c : LookupRelation.Config) (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (8*LookupStackWords c)) (8*LookupStackWords c)

def LookupLiveStack (c : LookupRelation.Config) (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (8*LookupStackWords c)) (8*LookupStackWords c+8)

def LookupBucketBytes (c : LookupRelation.Config) (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  InRange (c.table + .ofNat 64 (8*(c.query%8192))) 8 a ∨
  ∃ e ∈ v.bucket, BucketShapeReads (LookupRelation.ownerAddress c e.owner) a

def LookupOwnerBytes (c : LookupRelation.Config) (a : BitVec 64) : Prop :=
  ∃ owner, c.focus.owner = some owner ∧ InRange (LookupRelation.ownerAddress c owner) 8 a

def LookupCountBytes (c : LookupRelation.Config) (a : BitVec 64) : Prop :=
  ∃ pid, c.focus.peer = some pid ∧ InRange (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 a

def LookupDataWrites (c : LookupRelation.Config) (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  LookupOwnerBytes c a ∨ ((∃ n, v.count = some n ∧ n ≠ 0) ∧ LookupCountBytes c a)

/-- A conditional output requirement, not a count bound on the entry domain.
    Dead, NULL, miss and rejected-saturation inputs need no output storage. -/
def LookupOutputNeeded (v : LookupRelation.View) : Prop :=
  ∃ n, v.count = some n ∧ n ≠ 0 ∧ n+1 < 2^31

def LookupOutputWrites (v : LookupRelation.View) (s : MachineState) (a : BitVec 64) : Prop :=
  LookupOutputNeeded v ∧ InRange s.data.regs.rcx.toBitVec 8 a

def LookupPendingRead (preempt : BitVec 32) : Prop := (preempt+1) &&& 0x00ffff00 = 0

/-- Named physical entry obligations. Separation is an explicit allocation
    discipline, not a claim that every safe x86 alias is admitted. No live-
    peer or positive-count invariant is imposed. Every byte range belongs
    to lookup, its helper, its stack or its named service callbacks. -/
structure LookupEntry (c : LookupRelation.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (returnAddress : UInt64) (s : MachineState)
    (world : Leanux.World) (v : LookupRelation.View) : Prop where
  pc : s.pc = Image.Lookup.entry
  frame : EntryFrame s returnAddress
  table : s.data.regs.rdi.toBitVec = c.table
  query : (s.data.regs.get (.low .rdx .W32)).toNat = c.query
  kinds : KindMask (s.data.regs.get (.low .rsi .W32)) c.kinds
  projected : LookupRelation.project c world = some v
  focus : LookupRelation.EntryFocus c v
  physical : LookupRelation.Physical c [s] [LookupObservation.call "wg_index_hashtable_lookup" s] s v
  steps : world.steps.toList = c.incomingSteps
  rxSection : world.netRxSection = c.rxSection
  coverageAt : LookupCoverageAt coverage preempt v s.data.dmem
  preemptAt : load32 s.data.dmem preemptCountAddress = some preempt
  stackMapped : ∀ n < LookupStackWords c,
    (s.data.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true
  outputMapped : LookupOutputNeeded v → (s.data.dmem.loadInt s.data.regs.rcx.toBitVec 8).isSome = true
  bhHardirq : (512+preempt) &&& 0x000f0000 = 0
  bhPending : LookupPendingRead preempt → s.data.dmem.loadInt softirqPendingAddress 2 = some 0
  readsScratch : ∀ a, LookupRelation.Reads c v a →
    ¬(LookupStackWrites c s a ∨ LookupCoverageWrites coverage preempt v a ∨ InRange preemptCountAddress 4 a)
  serviceStack : ∀ a, LookupServiceBytes coverage preempt v a → ¬LookupStackWrites c s a
  coverageStack : ∀ a, LookupCoverageWrites coverage preempt v a → ¬LookupLiveStack c s a
  coverageMetadata : ∀ a, LookupCoverageWrites coverage preempt v a → ¬LookupMetadataBytes coverage preempt v a
  coveragePreempt : ∀ a, LookupCoverageWrites coverage preempt v a → ¬InRange preemptCountAddress 4 a
  bhStack : ∀ a, InRange preemptCountAddress 4 a → ¬LookupLiveStack c s a
  bhMetadata : ∀ a,
    (LookupMetadataBytes coverage preempt v a ∨
      (LookupBufferNeeded coverage preempt v ∧ KcovStorageBytes coverage a)) →
    ¬InRange preemptCountAddress 4 a
  dataService : ∀ a, LookupServiceBytes coverage preempt v a → ¬LookupDataWrites c v a
  dataReturn : ∀ a, InRange s.data.regs.rsp.toBitVec 8 a → ¬LookupDataWrites c v a
  dataBucket : ∀ a, LookupBucketBytes c v a → ¬LookupDataWrites c v a
  ownerCount : ∀ a, LookupCountBytes c a → ¬LookupOwnerBytes c a
  outputProtected : ∀ a, LookupOutputWrites v s a →
    ¬(LookupRelation.Reads c v a ∨ LookupServiceBytes coverage preempt v a ∨
      InRange (s.data.regs.rsp.toBitVec-48) 56 a ∨ LookupCoverageWrites coverage preempt v a)
  pendingFrame : LookupPendingRead preempt → ∀ a, InRange softirqPendingAddress 2 a →
    ¬(LookupStackWrites c s a ∨ LookupCoverageWrites coverage preempt v a ∨
      LookupDataWrites c v a ∨ LookupOutputWrites v s a)

/-- Entry domain relative to the supplied source World and fixed ABI/address
    interpretation. Its machine-side domain existentially closes world and
    these interpretation parameters. No execution or R-preservation premise
    occurs here; LookupWitness supplies a concrete inhabitant and its test
    executes that exact state to the recorded return. -/
def Pre_lookup (c : LookupRelation.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (returnAddress : UInt64) (s : MachineState) (world : Leanux.World) : Prop :=
  ∃ v, LookupEntry c coverage preempt returnAddress s world v

end Binary.TrustBase
```


### Milestone-1 review fix F1: hit-domain witnesses (2026-10-15)

[USER] Finish the independent review changes in the stated order, one commit
per finding, then proceed directly to milestone 2; that review rechecks these
fixes. No separate review is required before milestone 2.

`LookupHitWitness.dead_pre` and `live_pre` prove the unchanged `Pre_lookup`
for concrete selected-handshake states. Unlike the miss witness, they exercise
the owner and count representation, thirteen stack words, and (on the live
path) the output mapping and separation clauses. The live read projection is
checked against operation 3 of `d1_second_response`; the zero-count mutation
is a witness to the admitted domain, not to kernel reachability. Finding 1
remains recorded; neither Pre nor R was narrowed.

The exact Lean states executed to the original return: dead **441 instructions,
14 points**, live **506 instructions, 15 points**, each at two undefined-value
seeds. ABI registers/stack, owner word, reference count, output and ordered
mirror decisions agree. The live run also matches the recorded reference
probe's coverage and operands. Reproduction: `binary/run.py --trace
 d1_second_response` (or its completed `--check` directory), then from
`binary/`, `capped -- lake env lean LookupHitWitnessTest.lean`. This run reused
`.artifacts/check/binary-tv-20261015-024837`; the three-way check passed before
the exact-state tests. Both witness declarations are included in the binary
axiom gate. Their only axioms are `propext`, `Classical.choice`, `Quot.sound`.
No callback contract was used to shortcut the concrete executions.
The default build (353 jobs), binary axiom/escape gate, fresh
`leanchecker LookupHitWitness` closure replay and unit tier (126 tests,
one skip) all passed.

Development elaboration failures were fixed before these passes; no killed
or timed-out run was counted as success. F3 and later findings remain open.


### Milestone-1 review fix F3: explicit environment surface (2026-10-15)

[USER] Serialization and permissions are explicit headline hypotheses.
`lookup_simulation` and all three transport headlines now take
`SerializedEnvironment onlineCPUs externalActions` and
`InvocationPermissions fetch permissions initial outerRetPC`. The latter is
safety over finite actual instruction prefixes through the first outer RET;
it assumes no termination, mirror result, source decisions, or R preservation.
The conclusion exports `RunEnvironment` on the same raw history, including
service interiors and RET's stack read, excluding the unexecuted caller
continuation. The underlying Kraken execution theorem remains proved without
these hypotheses; the permission audit is then derived from the access
premise. Serialization is the explicitly supplied external interpretation,
re-exported unchanged, not verification of a real scheduler or interrupt log.

The implementation proves that the raw trace consists of actual successors,
that the accepted source has exactly one outer-return tag, and that the final
raw edge is the compiled outer RET. The last fact was present internally in
the seven-instruction epilogue but absent from the old postcondition. These
facts justify the audit's invocation boundary; none is a new assumption.
`Pre_lookup`, its witnesses and R are unchanged.

Unused `WholeImageDecoderAgreement`, `AnchoredTextStable` and `ReadOnlyImage`
were removed. Stable text and absence of GS use are explicitly external
interpretation facts, alongside the ELF/decoder link: the independent review
measured no alternatives entry in the anchored ranges, no jump table, empty
smp_locks and no RET-thunk rewrite. The five callback contracts remain
hypotheses until F2, due before milestone 4's first transport.

Validation: default build **357 jobs PASS**, binary axiom/escape gate PASS,
and fresh `leanchecker LookupSnapshotTransport` closure replay PASS. The
internal read-only check found no correctness defect; it noted that the access
predicate rejects fault/unimplemented effects as well as denied permissions.
The underlying Kraken theorem proves successful execution independently of
that premise. No native-verification axiom or new project axiom was added.
The external gate at 430ea90 does not cover this changed surface; the next
external export must be regenerated. No KILLED banner or timeout occurred.


### Milestone-1 review fix F4: return service state (2026-10-15)

`LookupPost` now exports `LookupCoverageAt coverage preempt v` for the
entry view, the restored 32-bit preempt count, and the conditional
`LookupPendingRead preempt → loadInt softirqPendingAddress 2 = some 0`.
The coverage fact is preserved through BH-enable by its proved footprint;
the count follows from the existing balance contract and the epilogue's
memory equality. The pending word follows from the full-function footprint.
No premise, Pre clause or R clause changed; TrustBase is unchanged.

These are the service-state clauses needed when composing calls with the
same read context. They do not invent mapping for an inactive coverage buffer
or an unread pending word. A later call that reads more (for example a
nonempty-bucket comparison after an empty-bucket mode-3 lookup) still needs
those additional mapping/readiness facts from its caller frame/environment.
The exact hit-state tests now also check preempt/pending values and the KCOV
header bound after return.

Validation: default build (357 jobs) and binary axiom/escape gate PASS; both
exact hit executions PASS (441/506 instructions, two seeds each), including
the added service-state assertions. Only the three standard axioms occur.
No KILLED banner or timeout occurred. External export replay will cover the
updated surface at the milestone-2 claim point.


### Milestone-1 review fix F5: composition correction (2026-10-15)

`compose_regions` was unused. Milestone 1's composition is bespoke, through
`selected_execution`, `miss_execution` and their per-path helper lemmas;
region statements were hand-written, not generated from the correspondence
table. The original gate's no-axiom result for `compose_regions` was true but
irrelevant to the headline. It was not the charter's proposed one-time
composition theorem. [AGENT] Retire the unused lemma and its gate/README
claim rather than retain an unused artifact as evidence of composition.
The historical handoff above describes the old checkpoint; this correction
supersedes its presentation of that helper.

The measured milestone-1 rate remains 54 hand-finished region identities in
16.98 elapsed hours, zero automated regions; it is not aggregate agent labor.
It supports no campaign-wide throughput forecast. Milestone 2 will report
proof lines per anchored instruction and primary/read-only-agent effort, and
target automation of repeated instruction-step/frame plumbing rather than
claim a generic composition that is not used.

Validation: default build (357 jobs) and binary gate PASS after removal. No
Lean source references `compose_regions`; headline proofs and their axiom
sets are unchanged. No KILLED banner or timeout occurred.


### Milestone-1 review fix F8: pin and surface drift gate (2026-10-15)

The binary gate now requires the private Kraken HEAD to match both the lock
and `TrustBase.krakenCommit`, verifies the resolved Lake path, and rejects
tracked changes or untracked source files before building. Ignored build
outputs are permitted. The concrete probe uses the same read-only pin check.
The gate prints the headline types, R/postcondition, finite-history and
return-boundary definitions, and verbatim `TrustBase.lean`, then diffs the
explicit `binary/TrustSurface.expected.txt` specification. An intentional
surface change requires a visible baseline diff; the gate does not rewrite it.
[AGENT] Include the finite-history definitions because they determine the
meaning of the new environment premise; names alone would hide that change.

Validation: the updated binary gate PASS. Six small tests PASS: clean tree
with ignored build output, rejected tracked edit, rejected untracked source,
rejected changed HEAD, rejected trust/lock disagreement, and visible changed
premise in the surface diff. Fixture repositories are temporary and deleted.
The default build and all headline/witness axioms remain clean. No KILLED
banner or timeout occurred. This local gate is distinct from external
`lake check --from-export`; the README's complete external recipe is the
remaining documentation item after F11.


### Milestone-1 review fix F10: scoped capture and isolated examples (2026-10-15)

Raw `LEANUX_BINARY_PCS`/`LEANUX_BINARY_CMP` output is now opt-in via
`evaluator.check --binary-coverage`, which the standalone probe requests.
The host resolves the two M1 function ranges from the identity-checked ELF's
symbol addresses and sizes; missing or ambiguous symbols fail. The guest
receives those ranges as an input file and contains no s4 address constants.
Ordinary runs install no range file and emit no raw binary stream. The
existing differential coverage remains unchanged.

The branch-added binary-gate paragraph in AGENTS.md is reverted. It wanted
to make the standalone charter gate discoverable beside the mirror proof
gate; that was a proposed standing-rule edit, not needed for the authorized
charter task. Commands and their claim scope live in binary/README.md. The
16-slot setting is retained: [USER 2026-10-15] explicitly requested
`LEANUX_QEMU_SLOTS=16` for this track, overriding the older 8-slot practice.

The private Kraken patch isolates **all three** unfinished example proofs
(the two in Examples.lean and the one in IncrementDMA.lean), preserving the
files as `.lean.txt` under `notes/unfinished-examples/`, outside every Lean
library glob and import. The root import is removed. No ISA semantics changed.
The new clean pin is `e91a885e02f5ac6e63bacf1de10733f9a0b7e788`; the lock,
TrustBase and reviewed surface specification agree. Reapplying the three
patches to upstream `8af7806` reproduces that exact clean commit.

Validation: 132 unit tests PASS (one skip), plus two range-resolution tests
PASS; the private Kraken default build (67 jobs), binary default build
(357 jobs), and binary pin/axiom/surface gate PASS. A fresh ordinary
same-bucket-miss differential run passes (one trace, six operations) with
zero raw binary lines; a fresh opt-in miss run passes the three-way comparison.
The exact Lean miss witness executes 191 instructions to return with six
points and two undefined-value seeds. No KILLED banner or timeout occurred.
The fresh opt-in live-hit run also passes the three-way comparison (one
trace, six operations); both exact hit witnesses execute to return again:
dead 441 instructions/14 points, live 506/15, two undefined-value seeds each.


### Milestone-1 review fix F11: limits after the fixes (2026-10-15)

This list supersedes the historical handoff's “what this does not say”.

- **Entry witnesses and reachability.** Miss, live-hit and dead-hit Pre states
  now have Lean witnesses and execute to return (F1). They are materialized
  from the recorded read projection; the dead state is a zero-count mutation.
  This does not prove that the kernel reaches that dead entry. The NULL-owner,
  wrong-kind and all callback-mode combinations do not each have a formal Pre
  witness. Finding 1 remains recorded; no dead-peer exclusion was added to
  Pre or R. The lifecycle claim that no modeled path reads a zero-count peer
  before RCU release remains a separate obligation when those paths are proved.
- **Environment.** Serialization and invocation permissions are now explicit
  headline hypotheses (F3), not verified scheduler/interrupt records or a
  hardware paging model. The permission premise is safety for every actual
  finite prefix through RET, including undefined effects; it assumes no
  termination or simulation. The serialization audit repeats the supplied
  single-CPU/no-interleaving premise.
- **Return state and composition.** F4 exports the restored preempt count,
  coverage-buffer invariant and conditionally read softirq-pending word.
  These suffice for the same read context, not every later call: new callback
  reads, mappings, separation and shared address interpretation remain caller
  obligations. `c.peers` and `c.keypairs` interpret identities per invocation;
  they are not a global allocation map. Composition must share coherent
  interpretations. Physical allocator membership and absence are not proved.
- **Transport.** Generic `P` has binary meaning through the fields R relates.
  Untouched fields use a source frame theorem and the binary write footprint,
  plus initial representation and separation premises. Those extra premises
  are still unwitnessed and must be discharged by the composition's global
  invariant. No counter-window, R1–R6 or H1–H6 result is yet carried to an
  entire binary operation or trace unconditionally. The instantiated snapshot
  transport is conditional in precisely this way; it is not an allocator
  invariant or a whole receive-path theorem.
- **Records.** Lookup has no record-consuming hooks. Section 1's record-stream
  parameter is unexercised until milestone 3. Matching lookup's accepted
  source decisions proves no whole-operation/whole-trace scheduling theorem.
- **Coverage.** Service contracts specify planned KCOV writes and F4 exports
  buffer readiness; the headline does not identify the entire resulting KCOV
  log with a recorded kernel log. Coverage is test evidence, not a WireGuard
  observable. The kernel comparisons are separate concrete tests.
- **Services and realism.** Five callback contracts are explicit assumptions,
  to be proved from the image before milestone 4's first transport (F2).
  Milestone 4 must check actual entries against Pre (F7), especially the zero
  pending-softirq requirement on the BH-enable read path (which excludes
  `do_softirq` inside this call), the user-writable KCOV header bound and the
  nonzero bucket-node addresses. No fixture-specific reachability invariant
  has silently narrowed the dead-peer branch.
- **External interpretation and proof trust.** ELF identity, binutils decoding,
  DWARF and Kraken's correspondence to hardware remain external. The theorem
  is about its pinned x86-64 model, not concurrent weak-memory hardware,
  timing or microarchitectural behavior. The proof uses only `propext`,
  `Classical.choice` and `Quot.sound`; F10 quarantines the three unfinished
  upstream example proofs outside compiled Lean sources. The external kernel
  gate accepted checkpoint 430ea90 only; it must be rerun over a fresh export
  for the changed surface. A local build/axiom check is not that external gate.
- **Method and rate.** Composition is bespoke; `compose_regions` was unused
  and is retired (F5). The measured rate is 54 hand-finished region identities
  in 16.98 elapsed hours, zero automated regions, not aggregate agent labor.
  Roughly 28,000 proof lines for 138 anchored instructions is about 200 lines
  per instruction, not evidence of campaign-wide throughput. M2 will measure
  its own proof size and effort and target repeated step/frame plumbing.

[USER 2026-10-15] Proceed directly to milestone 2 after these fixes; its
independent review rechecks the milestone-1 fixes. No separate review is
requested before then. The existing review's go verdict is conditional on
these dispositions, not a fresh approval of their implementation.

The current milestone-1 trust base follows verbatim. The earlier quotation
is historical; this one includes F3's named invocation hypotheses and F10's
private Kraken pin. No premise is omitted from the quotation.

```lean
import FiniteExecution
import Image
import ServiceImage
import Memory
import LookupProjection

/-! Named trust surface for the pinned lookup proof, under construction.
    These are explicit hypotheses, not globally asserted facts. No declaration
    here assumes the lookup result, a region's R-preservation, or a mirror run.
    Pre_lookup is accompanied by its concrete satisfying witness.
    The final milestone report must reproduce this file verbatim.

    External interpretation: binutils 2.42 supplied the literal AST and DWARF
    layouts from the ELF below. Lean checks execution of those terms, not the
    binutils decoder, DWARF producer, SHA computation or correspondence of
    Kraken's model with x86 hardware. The loader checks identity and branch
    encodings. Mutable runtime globals are NOT assumed equal to ELF initial
    bytes at a function entry; their current values belong in Pre_lookup.
    A fixed fetch models stable text; the external ELF interpretation requires
    no runtime text patch in these ranges. Independent review measured no
    alternatives entry in the ranges, no jump table, empty smp_locks, no RET
    thunk rewriting, and no GS use. These are interpretation facts, not unused
    Lean premises. Permissions and serialization below are headline hypotheses.

-/
namespace Binary.TrustBase

def krakenCommit : String := "e91a885e02f5ac6e63bacf1de10733f9a0b7e788"
def kernelIdentity : String := "6b2018b9"
def elfSha256 : String := "16c346209885db6c610d4aa126c6eb30f5d3c02f0498d95e606473945f648774"
def decoderVersion : String := "GNU objdump (GNU Binutils for Ubuntu) 2.42"

local instance : Labels := Image.linkedLabels

/-- The partial linked decoder for both anchored functions and all reached
    service bodies. A rejected instruction remains a failing fetch; neither
    its semantics nor successful execution is assumed by this definition. -/
def pinnedFetch (pc : Int64) : Option Decoded :=
  (Image.fetch pc).orElse (fun _ => ServiceImage.fetch pc)

/-- The ambient decoder agrees with the pinned literal instructions/lengths.
    Interpreting those literals as this ELF is the external decoding assumption. -/
def AnchoredDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, Image.fetch pc = some instruction → fetch pc = some instruction

/-- External paging/access permissions, absent from Kraken MachineState. -/
structure Permissions where
  read : BitVec 64 → Width → Prop
  write : BitVec 64 → Width → Prop
  execute : Std.Rco Int64 → Prop

/-- Kraken's All grants permission requests. This separate premise makes
    that grant explicit for every effect, including every undefined outcome. -/
def AccessAllowed (permissions : Permissions) : Effects → Prop
  | .done _ => True
  | .unimplemented _ | .gp_unaligned .. | .nonmem_load .. | .nonmem_store .. => False
  | @Effects.undefined α _ next => ∀ value : α, AccessAllowed permissions (next value)
  | .require_read_access address width next =>
      permissions.read address width ∧ AccessAllowed permissions (next ())
  | .require_write_access address width next =>
      permissions.write address width ∧ AccessAllowed permissions (next ())
  | .require_exec_access pc next =>
      permissions.execute pc ∧ AccessAllowed permissions (next ())

/-- Every actually executed instruction has its requested accesses granted;
    the final return destination is not itself executed by this run. -/
def RunAccessAllowed (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (history : List MachineState) : Prop :=
  ∀ s ∈ history.dropLast, ∃ decoded, fetch s.pc = some decoded ∧
    permissions.execute ⟨s.pc, s.pc + .ofNat decoded.size⟩ ∧
    AccessAllowed permissions
      (decoded.instruction.interp s.data ⟨s.pc, s.pc + .ofNat decoded.size⟩
        (fun d => .done ⟨d, s.pc + .ofNat decoded.size⟩) (fun pc d => .done ⟨d, pc⟩))

/-- The environment places no interrupt, preemption or competing CPU action
    inside this anchored call; the records place such actions between calls. -/
structure SerializedEnvironment (onlineCPUs : Nat) (externalActions : List Nat) : Prop where
  singleCPU : onlineCPUs = 1
  noInterleaving : externalActions = []

/-- Permission safety of finite actual prefixes through the first outer RET.
    This is safety only: no termination, source result or relation is assumed.
    Service interiors are included; the unexecuted return destination is not. -/
def InvocationPermissions (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (initial : MachineState) (returnPC : Int64) : Prop :=
  ∀ history, ActualHistory fetch initial history → NoEarlyReturn returnPC history →
    RunAccessAllowed fetch permissions history

/-- The exported interpretation audit of this actual instruction history. -/
def RunEnvironment (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (onlineCPUs : Nat) (externalActions : List Nat) (history : List MachineState) : Prop :=
  SerializedEnvironment onlineCPUs externalActions ∧ RunAccessAllowed fetch permissions history

/-- Kernel ABI: the stack word is the actual CALL return address. Eight-byte
    alignment follows this kernel's compiler flags, not a userspace ABI guess. -/
def EntryFrame (s : MachineState) (returnAddress : UInt64) : Prop :=
  s.data.regs.rsp.toNat % 8 = 0 ∧
  s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8 = some (returnAddress.toNat : Int)

/-- Only ABI-preserved registers are constrained; caller-save registers and
    flags may change. The callee has consumed the actual return-address word. -/
def Returned (entry final : MachineState) (returnAddress : UInt64) : Prop :=
  final.pc = .ofBitVec returnAddress.toBitVec ∧
  final.data.regs.rsp = entry.data.regs.rsp + 8 ∧
  final.data.regs.rbx = entry.data.regs.rbx ∧
  final.data.regs.rbp = entry.data.regs.rbp ∧
  final.data.regs.r12 = entry.data.regs.r12 ∧
  final.data.regs.r13 = entry.data.regs.r13 ∧
  final.data.regs.r14 = entry.data.regs.r14 ∧
  final.data.regs.r15 = entry.data.regs.r15

/-- Service internals emit no anchored observation or cut. The final state
    may return to an anchored address; it is deliberately not excluded. -/
def NoAnchoredReentry (history : List MachineState) : Prop :=
  ∀ s ∈ history.dropLast, Image.fetch s.pc = none

/-- A service contract uses the same fetched-instruction execution as the
    function proof. Its readiness and write footprint are physical predicates;
    their concrete instantiations must be part of the witnessed entry domain. -/
def ServiceReturns (fetch : Int64 → Option Decoded) (address : Int64)
    (ready : MachineState → Prop) (writes : MachineState → BitVec 64 → Prop)
    (effect : MachineState → MachineState → Prop) : Prop :=
  ∀ s returnAddress, s.pc = address → ready s → EntryFrame s returnAddress →
    Eventually (historyStep fetch)
      (fun t => Returned s t.machine returnAddress ∧
        EqualOutside (writes s) s.data.dmem t.machine.data.dmem ∧
        effect s t.machine ∧ NoAnchoredReentry t.history)
      ⟨s, [s]⟩

def preemptCountAddress : BitVec 64 := .ofNat 64 0xffffffff81cc85c8
def currentTaskAddress : BitVec 64 := .ofNat 64 0xffffffff81cc85c0
def softirqPendingAddress : BitVec 64 := .ofNat 64 0xffffffff81cc85e0

inductive KcovKind where
  | pc | cmp4 | constCmp4 | constCmp1
  deriving DecidableEq

structure WordWrite where
  address : BitVec 64
  value : BitVec 64

def load64 (memory : Mem 64) (address : BitVec 64) : Option (BitVec 64) :=
  (memory.loadInt address 8).map (.ofInt 64)

def load32 (memory : Mem 64) (address : BitVec 64) : Option (BitVec 32) :=
  (memory.loadInt address 4).map (.ofInt 32)

/-- Physical callback metadata, fixed during an anchored call except for the
    separately balanced preempt count. Capacity is a count of 64-bit words. -/
structure KcovLayout where
  task : BitVec 64
  area : BitVec 64
  capacity : BitVec 32
  mode : BitVec 32
  softirqEnabled : BitVec 32

/-- Exact runtime metadata reads, not the ELF's initial global bytes. -/
def KcovMetadata (layout : KcovLayout) (memory : Mem 64) : Prop :=
  load64 memory currentTaskAddress = some layout.task ∧
  load32 memory (layout.task + 0x6e0) = some layout.mode ∧
  load32 memory (layout.task + 0x6e4) = some layout.capacity ∧
  load64 memory (layout.task + 0x6e8) = some layout.area ∧
  load32 memory (layout.task + 0x704) = some layout.softirqEnabled

/-- Mapped buffer and bounded runtime header. A full buffer is allowed; no
    callback is required to have room for a record. This predicate says
    nothing about the peer state or the lookup result. -/
def KcovBuffer (layout : KcovLayout) (memory : Mem 64) : Prop :=
  (∀ word < layout.capacity.toNat,
    (memory.loadInt (layout.area + .ofNat 64 (8 * word)) 8).isSome = true) ∧
  ∃ count : Nat, count ≤ layout.capacity.toNat ∧
    load64 memory layout.area = some (.ofNat 64 count)

def KcovBufferBytes (layout : KcovLayout) : BitVec 64 → Prop :=
  InRange layout.area (8 * layout.capacity.toNat)

/-- Storage read by an active callback. Even capacity zero still requires
    the header; caller writes must preserve it as well as the buffer words. -/
def KcovStorageBytes (layout : KcovLayout) (address : BitVec 64) : Prop :=
  InRange layout.area 8 address ∨ KcovBufferBytes layout address

def KcovMetadataBytes (layout : KcovLayout) (address : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 address ∨
  InRange (layout.task + 0x6e0) 4 address ∨
  InRange (layout.task + 0x6e4) 4 address ∨
  InRange (layout.task + 0x6e8) 8 address ∨
  InRange (layout.task + 0x704) 4 address

/-- Physical disjointness from protected memory (metadata, live stack and
    represented objects). Readiness is proved from this, not assumed at
    every callback. The caller chooses the actual protected footprint. -/
def KcovSeparated (layout : KcovLayout) (protectedBytes : BitVec 64 → Prop) : Prop :=
  ∀ address, KcovBufferBytes layout address → ¬protectedBytes address

/-- Physical state carried between callbacks. Disabled tracing requires no
    mapped coverage area; the mode field itself still belongs to the task. -/
def KcovState (layout : KcovLayout) (preempt : BitVec 32) (memory : Mem 64) : Prop :=
  KcovMetadata layout memory ∧
  load32 memory preemptCountAddress = some preempt ∧
  (layout.mode = 2 ∨ layout.mode = 3 → KcovBuffer layout memory)

/-- Bytes that caller stores must preserve. Buffer storage is needed only
    in an active mode; metadata and preemption state are always physical. -/
def KcovStateBytes (layout : KcovLayout) (address : BitVec 64) : Prop :=
  KcovMetadataBytes layout address ∨ InRange preemptCountAddress 4 address ∨
    ((layout.mode = 2 ∨ layout.mode = 3) ∧ KcovStorageBytes layout address)

/-- Physical KCOV callback specification, with the actual early-return read
    dependencies and machine-width arithmetic. It is not a proof checker. -/
def KcovPlan (kind : KcovKind) (s : MachineState) : Option (List WordWrite) := do
  let memory := s.data.dmem
  let preempt ← load32 memory preemptCountAddress
  let returnPC ← load64 memory s.data.regs.rsp.toBitVec
  let task ← load64 memory currentTaskAddress
  if preempt &&& 0xff0100 != 0 then
    if preempt &&& 0x100 == 0 || preempt &&& 0xff0000 != 0 then return []
    let softirqEnabled ← load32 memory (task + 0x704)
    if softirqEnabled == 0 then return []
  let mode ← load32 memory (task + 0x6e0)
  if mode != (if kind = .pc then 2 else 3) then return []
  let area ← load64 memory (task + 0x6e8)
  let capacity ← load32 memory (task + 0x6e4)
  let count ← load64 memory area
  if kind = .pc then
    let next := count + 1
    if next.toNat ≥ capacity.toNat then return []
    return [⟨area, next⟩, ⟨area + 8 * next, returnPC⟩]
  else
    let slot := 4 * count
    let ending := 8 * slot + 40
    if 8 * (capacity.setWidth 64) < ending then return []
    let tag : BitVec 64 := match kind with
      | .pc => 0
      | .cmp4 => 4
      | .constCmp4 => 5
      | .constCmp1 => 1
    let arg1 := if kind = .constCmp1 then (s.data.regs.get (.low .rdi .W8)).setWidth 64
      else (s.data.regs.get (.low .rdi .W32)).setWidth 64
    let arg2 := if kind = .constCmp1 then (s.data.regs.get (.low .rsi .W8)).setWidth 64
      else (s.data.regs.get (.low .rsi .W32)).setWidth 64
    return [⟨area, count + 1⟩, ⟨area + ending - 32, tag⟩,
      ⟨area + ending - 24, arg1⟩, ⟨area + ending - 16, arg2⟩,
      ⟨area + ending - 8, returnPC⟩]

/-- Planned destinations are mapped and do not overwrite the return word.
    Separation from all represented objects is an additional entry obligation. -/
def KcovReady (kind : KcovKind) (s : MachineState) : Prop :=
  ∃ stores, KcovPlan kind s = some stores ∧
    ∀ write ∈ stores,
      (s.data.dmem.loadInt write.address 8).isSome = true ∧
      ∀ address, InRange write.address 8 address → ¬InRange s.data.regs.rsp.toBitVec 8 address

def KcovWrites (kind : KcovKind) (s : MachineState) (address : BitVec 64) : Prop :=
  ∃ stores, KcovPlan kind s = some stores ∧
    ∃ write ∈ stores, InRange write.address 8 address

/-- Exact callback stores keep repeated-call buffer readiness provable;
    allowing arbitrary corruption of the coverage buffer would not suffice. -/
def KcovEffect (kind : KcovKind) (before after : MachineState) : Prop :=
  ∃ stores, KcovPlan kind before = some stores ∧
    after.data.dmem = stores.foldl
      (fun memory write => memory.storeInt write.address 8 write.value.toInt) before.data.dmem

/-- KCOV PC callback: only its physically planned stores may occur. -/
def TracePcContract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)

/-- KCOV variable/variable 32-bit comparison callback. -/
def TraceCmp4Contract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3e80) (KcovReady .cmp4) (KcovWrites .cmp4) (KcovEffect .cmp4)

/-- KCOV constant/variable 32-bit comparison callback. -/
def TraceConstCmp4Contract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3f00) (KcovReady .constCmp4)
    (KcovWrites .constCmp4) (KcovEffect .constCmp4)

/-- KCOV constant/variable 8-bit comparison callback used by peer-get. -/
def TraceConstCmp1Contract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810f3ec0) (KcovReady .constCmp1)
    (KcovWrites .constCmp1) (KcovEffect .constCmp1)

/-- The actual no-work BH-enable path, including nested disable counts.
    The softirq word is needed only on the branch that reads it. -/
def BhEnableReady (s : MachineState) : Prop :=
  ∃ count : BitVec 32,
    s.data.dmem.loadInt preemptCountAddress 4 = some (count.toNat : Int) ∧
    count &&& 0x000f0000 = 0 ∧
    ((count + 1 - s.data.regs.get (.low .rsi .W32)) &&& 0x00ffff00 = 0 →
      s.data.dmem.loadInt softirqPendingAddress 2 = some 0) ∧
    ∀ address, InRange preemptCountAddress 4 address → ¬InRange s.data.regs.rsp.toBitVec 8 address

/-- BH enable balances the actual low-32-bit count argument, modulo 2^32.
    Readiness must justify that its softirq path runs no pending work. -/
def BhEnableContract (fetch : Int64 → Option Decoded) : Prop :=
  ServiceReturns fetch (.ofNat 0xffffffff810732c0) BhEnableReady
    (fun _ => InRange preemptCountAddress 4)
    (fun before after => ∀ old : BitVec 32,
      before.data.dmem.loadInt preemptCountAddress 4 = some (old.toNat : Int) →
      after.data.dmem.loadInt preemptCountAddress 4 =
        some ((old - before.data.regs.get (.low .rsi .W32)).toNat : Int))

/-- Whether the actual callback reads softirqEnabled before its mode test. -/
def LookupSoftRead (preempt : BitVec 32) : Prop :=
  preempt &&& 0xff0100 ≠ 0 ∧
  ¬(preempt &&& 0x100 = 0 ∨ preempt &&& 0xff0000 ≠ 0)

/-- The callback reaches its mode read only after the preemption/softirq gate. -/
def LookupModeRead (coverage : KcovLayout) (preempt : BitVec 32) : Prop :=
  if preempt &&& 0xff0100 ≠ 0 then
    ¬(preempt &&& 0x100 = 0 ∨ preempt &&& 0xff0000 ≠ 0) ∧ coverage.softirqEnabled ≠ 0
  else True

/-- PC callbacks occur before and after BH-disable. Comparisons occur only
    with a nonempty selected bucket, after the actual modular increment. -/
def LookupBufferNeeded (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) : Prop :=
  (coverage.mode = 2 ∧ (LookupModeRead coverage preempt ∨ LookupModeRead coverage (512+preempt))) ∨
  (coverage.mode = 3 ∧ v.bucket ≠ [] ∧ LookupModeRead coverage (512+preempt))

/-- Only callback metadata reached in one of this lookup's two contexts.
    Unused layout values impose no equality on memory. The active coverage
    allocation is mapped uniformly; a full buffer is permitted. -/
def LookupCoverageAt (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (memory : Mem 64) : Prop :=
  load64 memory currentTaskAddress = some coverage.task ∧
  ((LookupSoftRead preempt ∨ LookupSoftRead (512+preempt)) →
    load32 memory (coverage.task+0x704) = some coverage.softirqEnabled) ∧
  ((LookupModeRead coverage preempt ∨ LookupModeRead coverage (512+preempt)) →
    load32 memory (coverage.task+0x6e0) = some coverage.mode) ∧
  (LookupBufferNeeded coverage preempt v →
    load32 memory (coverage.task+0x6e4) = some coverage.capacity ∧
    load64 memory (coverage.task+0x6e8) = some coverage.area ∧ KcovBuffer coverage memory)

def LookupMetadataBytes (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 a ∨
  ((LookupSoftRead preempt ∨ LookupSoftRead (512+preempt)) ∧ InRange (coverage.task+0x704) 4 a) ∨
  ((LookupModeRead coverage preempt ∨ LookupModeRead coverage (512+preempt)) ∧ InRange (coverage.task+0x6e0) 4 a) ∨
  (LookupBufferNeeded coverage preempt v ∧
    (InRange (coverage.task+0x6e4) 4 a ∨ InRange (coverage.task+0x6e8) 8 a))

def LookupCoverageWrites (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  LookupBufferNeeded coverage preempt v ∧ KcovBufferBytes coverage a

def LookupServiceBytes (coverage : KcovLayout) (preempt : BitVec 32)
    (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  LookupMetadataBytes coverage preempt v a ∨ InRange preemptCountAddress 4 a ∨
  (LookupBufferNeeded coverage preempt v ∧ KcovStorageBytes coverage a)

/-- The helper is called for a selected owner even when its peer word is NULL. -/
def LookupStackWords (c : LookupRelation.Config) : Nat := if c.focus.owner.isSome then 13 else 6

def LookupStackWrites (c : LookupRelation.Config) (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (8*LookupStackWords c)) (8*LookupStackWords c)

def LookupLiveStack (c : LookupRelation.Config) (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (8*LookupStackWords c)) (8*LookupStackWords c+8)

def LookupBucketBytes (c : LookupRelation.Config) (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  InRange (c.table + .ofNat 64 (8*(c.query%8192))) 8 a ∨
  ∃ e ∈ v.bucket, BucketShapeReads (LookupRelation.ownerAddress c e.owner) a

def LookupOwnerBytes (c : LookupRelation.Config) (a : BitVec 64) : Prop :=
  ∃ owner, c.focus.owner = some owner ∧ InRange (LookupRelation.ownerAddress c owner) 8 a

def LookupCountBytes (c : LookupRelation.Config) (a : BitVec 64) : Prop :=
  ∃ pid, c.focus.peer = some pid ∧ InRange (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 a

def LookupDataWrites (c : LookupRelation.Config) (v : LookupRelation.View) (a : BitVec 64) : Prop :=
  LookupOwnerBytes c a ∨ ((∃ n, v.count = some n ∧ n ≠ 0) ∧ LookupCountBytes c a)

/-- A conditional output requirement, not a count bound on the entry domain.
    Dead, NULL, miss and rejected-saturation inputs need no output storage. -/
def LookupOutputNeeded (v : LookupRelation.View) : Prop :=
  ∃ n, v.count = some n ∧ n ≠ 0 ∧ n+1 < 2^31

def LookupOutputWrites (v : LookupRelation.View) (s : MachineState) (a : BitVec 64) : Prop :=
  LookupOutputNeeded v ∧ InRange s.data.regs.rcx.toBitVec 8 a

def LookupPendingRead (preempt : BitVec 32) : Prop := (preempt+1) &&& 0x00ffff00 = 0

/-- Named physical entry obligations. Separation is an explicit allocation
    discipline, not a claim that every safe x86 alias is admitted. No live-
    peer or positive-count invariant is imposed. Every byte range belongs
    to lookup, its helper, its stack or its named service callbacks. -/
structure LookupEntry (c : LookupRelation.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (returnAddress : UInt64) (s : MachineState)
    (world : Leanux.World) (v : LookupRelation.View) : Prop where
  pc : s.pc = Image.Lookup.entry
  frame : EntryFrame s returnAddress
  table : s.data.regs.rdi.toBitVec = c.table
  query : (s.data.regs.get (.low .rdx .W32)).toNat = c.query
  kinds : KindMask (s.data.regs.get (.low .rsi .W32)) c.kinds
  projected : LookupRelation.project c world = some v
  focus : LookupRelation.EntryFocus c v
  physical : LookupRelation.Physical c [s] [LookupObservation.call "wg_index_hashtable_lookup" s] s v
  steps : world.steps.toList = c.incomingSteps
  rxSection : world.netRxSection = c.rxSection
  coverageAt : LookupCoverageAt coverage preempt v s.data.dmem
  preemptAt : load32 s.data.dmem preemptCountAddress = some preempt
  stackMapped : ∀ n < LookupStackWords c,
    (s.data.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true
  outputMapped : LookupOutputNeeded v → (s.data.dmem.loadInt s.data.regs.rcx.toBitVec 8).isSome = true
  bhHardirq : (512+preempt) &&& 0x000f0000 = 0
  bhPending : LookupPendingRead preempt → s.data.dmem.loadInt softirqPendingAddress 2 = some 0
  readsScratch : ∀ a, LookupRelation.Reads c v a →
    ¬(LookupStackWrites c s a ∨ LookupCoverageWrites coverage preempt v a ∨ InRange preemptCountAddress 4 a)
  serviceStack : ∀ a, LookupServiceBytes coverage preempt v a → ¬LookupStackWrites c s a
  coverageStack : ∀ a, LookupCoverageWrites coverage preempt v a → ¬LookupLiveStack c s a
  coverageMetadata : ∀ a, LookupCoverageWrites coverage preempt v a → ¬LookupMetadataBytes coverage preempt v a
  coveragePreempt : ∀ a, LookupCoverageWrites coverage preempt v a → ¬InRange preemptCountAddress 4 a
  bhStack : ∀ a, InRange preemptCountAddress 4 a → ¬LookupLiveStack c s a
  bhMetadata : ∀ a,
    (LookupMetadataBytes coverage preempt v a ∨
      (LookupBufferNeeded coverage preempt v ∧ KcovStorageBytes coverage a)) →
    ¬InRange preemptCountAddress 4 a
  dataService : ∀ a, LookupServiceBytes coverage preempt v a → ¬LookupDataWrites c v a
  dataReturn : ∀ a, InRange s.data.regs.rsp.toBitVec 8 a → ¬LookupDataWrites c v a
  dataBucket : ∀ a, LookupBucketBytes c v a → ¬LookupDataWrites c v a
  ownerCount : ∀ a, LookupCountBytes c a → ¬LookupOwnerBytes c a
  outputProtected : ∀ a, LookupOutputWrites v s a →
    ¬(LookupRelation.Reads c v a ∨ LookupServiceBytes coverage preempt v a ∨
      InRange (s.data.regs.rsp.toBitVec-48) 56 a ∨ LookupCoverageWrites coverage preempt v a)
  pendingFrame : LookupPendingRead preempt → ∀ a, InRange softirqPendingAddress 2 a →
    ¬(LookupStackWrites c s a ∨ LookupCoverageWrites coverage preempt v a ∨
      LookupDataWrites c v a ∨ LookupOutputWrites v s a)

/-- Entry domain relative to the supplied source World and fixed ABI/address
    interpretation. Its machine-side domain existentially closes world and
    these interpretation parameters. No execution or R-preservation premise
    occurs here; LookupWitness supplies a concrete inhabitant and its test
    executes that exact state to the recorded return. -/
def Pre_lookup (c : LookupRelation.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (returnAddress : UInt64) (s : MachineState) (world : Leanux.World) : Prop :=
  ∃ v, LookupEntry c coverage preempt returnAddress s world v

end Binary.TrustBase
```

Validation: the quoted block is byte-for-byte TrustBase.lean; documentation
and register update only. F10’s successful build and gate cover the code.


### Milestone-1 README gate recipe (2026-10-15)

The README now gives the actual external gate form, from binary/:
`lake check --from-export ../.tmp/binary-m1.ndjson`, with `capped` around
heavy commands. It lists the leanexport modules (including the new hit
witness), requires a completed export from the claimed commit, distinguishes
inside-Nono speedbumps, and records why the sandboxed build cannot resolve
this package's parent path dependencies. The user-reported 430ea90 acceptance
and its original five modules remain explicitly historical. No external gate
for the changed surface is claimed; its fresh export belongs to the M2 claim
point. Exports are ephemeral and are not committed.

Validation: command syntax checked against the v4.35.0 toolchain's
LeanExport main and Lake Check --from-export option; documentation-only
change, no redundant proof rebuild. The next work is milestone 2, with the
independent M2 review rechecking all these M1 dispositions.


## Milestone 2: allowed-IPs lookup and common_bits (in progress)

Implementation began at approximately 20:41 UTC on 2026-10-15, after the
ordered M1 fixes. The image's local `lookup` at `0xffffffff813a0830` is the
chartered allowed-IPs lookup (103 instructions, 35 regions); `common_bits`
at `0xffffffff813a0750` contributes 73 instructions, 21 regions. The existing
peer-get helper is also called. The duplicate unrelated local `lookup`
symbol is rejected by source-qualified extraction. This is one milestone,
with one register row and this report updated across its commit series.

The automation target is repeated instruction-step and memory-frame plumbing,
using kernel-checked Lean proofs. There is no certificate checker. Reported
M2 instruction counts exclude previously certified peer-get and contracted
service bodies; elapsed time, primary work and delegated work will be stated
separately at the claim point. No M2 function-level theorem is claimed yet.

### BSR ISA extension

[AGENT 2026-10-15] Use the conservative common behavior of the current
[Intel SDM revision 089, BSR volume 2A page 3-109](https://cdrdv2-public.intel.com/868137/325462-089-sdm-vol-1-2abcd-3abcd-4.pdf)
and [AMD APM 24594 revision 3.37](https://docs.amd.com/api/khub/documents/j44LvPXzuuXgM0WyHKQfeQ/content).
Nonzero BSR returns the highest set-bit index. Zero preserves the destination;
32-bit zero additionally permits clearing its upper half, as Intel's
older-processor footnote allows. All five non-ZF arithmetic flags remain
universally undefined. This corrects the preliminary concern based on older
Intel wording quoted by Linux: no equal-key exclusion or vendor-specific
hypothesis is introduced. `common_bits` already seeds the zero input case
with -1 and initializes the relevant upper word to zero.

Private Kraken pin `7ebba06a30eaf08c10b26b28ca14bfee1c791576` adds semantics,
parser and both printers, 26 executable guards, four AT&T round trips, two
universal symbolic lemmas and a native assembly comparison. Tests cover all
three legal widths, zero/nonzero, both zero-W32 alternatives, source/destination
aliasing, memory-source/address-register aliasing, failed loads and illegal
operands. Full capped v4.35.0 build PASS (68 jobs), native comparison PASS
(1/1), and scoped fresh `leanchecker Kraken.X64.BsrTests` PASS; the symbolic
lemmas use only the three standard axioms.

A separate incidental `leanchecker --help` invocation **failed**, KILLED at
the unchanged 32 GB cap (exit 137): that tool ignored the flag and attempted
a whole-package replay. It is not counted as a pass. Dirty private and task
states were preserved to snapshot refs before further checks. The successful
scoped replay is a different, explicitly bounded check. An earlier command
using the private checkout's nightly toolchain failed in the elan shim;
Nono denial was unconfirmed. Subsequent commands selected the installed
v4.35.0 per process, with no global/toolchain-file change.

### Concrete test and proof foundations

Before the M2 function proof, fresh opt-in `b1_trie_routing` recording passed:
one trace, 12 operations, 102 compared operand pairs, 81 distinct rows.
`LEANUX_QEMU_SLOTS=16 capped -- python3 -B binary/allowedips_probe.py`
rebuilds that recording and the three-way comparison. IPv4 operation 5
returned peer 3 after 1,592 decoded instructions, 50 ordered PC records,
21 comparison triples and 34 mirror decisions; IPv6 operation 8 returned
peer 4 after 1,510 instructions, 47 PC records, 22 comparisons and 32
decisions. Both undefined-value seeds passed. The probe executes actual
common_bits, peer-get and coverage/service bodies, checks the ABI return,
and checks the materialised memory after its declared stack/KCOV framing.
The state is the recorded prefix's mirror read projection, with synthetic
addresses and explicit preempt baseline 512, not a captured kernel entry.
It is a test, not the required Lean witness for a future Pre_allowedips.
The existing M1 miss/hit tests still pass. Capture/harness unit checks passed
(16 tests, one existing skip).

The generated image has 176 instructions in 56 regions. The trie predicate
relates only the query-reachable nodes and bytes actually read: the low IPv6
key word is needed only after high-word equality. Its frame and subpath
lemmas check. No acyclicity, strictly increasing prefix, positive peer count,
or zero-valued placeholder bytes are imposed to make the proof terminate.
The mirror's accepted bounded run will supply the loop induction.

The named M2 service contracts add cmp1 and cmp8, and exclude reentry into
the new anchored ranges. They remain physical callback hypotheses; no
future R, expected source sequence, or termination of lookup is assumed.
The KCOV comparison tag/argument definitions are shared with its memory-plan
proof, including the full 64-bit cmp8 operands. M1's headline statements
are unchanged. The trust-surface baseline is updated explicitly for the
Kraken pin and these named declarations; they will be audited again with
M2's final headline. No Pre_allowedips declaration has landed yet.

Integrated capped build PASS (366 jobs), including all M1 headlines with
only propext, Classical.choice and Quot.sound. Intermediate failures remain
failures: broad arithmetic normalization was stopped twice (exit 143), and
one subsequent attempt was KILLED at a deliberately reduced 4 GB cap
(exit 137). A small explicit Nat normal form replaced it and checks in
under a second. Concurrent Lake dependency plans caused missing-olean
failures; dependency builds are now serialized while agents directly check
distinct new modules. The initial six-way KCOV proof timed out; the shared
tag/argument definitions and PC/non-PC split now check. These failures
are not included in passing counts. No cap was raised to obtain a pass.

The binary proof gate passes at this foundation checkpoint, including the
clean private dependency pin, headline axiom check, and printed/diffed trust
surface. This is the project gate, not a new external export replay.
