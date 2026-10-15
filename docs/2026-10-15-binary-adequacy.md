# Binary adequacy: work toward milestone 1

Milestone 1 is **not complete**. No function adequacy or transported mirror
property is claimed by the current region lemmas.

## Rule Zero finding 1: a dead index entry retains its peer in the mirror

[USER 2026-10-14] Keep every path, including the dead-peer branch; do not
narrow `Pre_f` to exclude it. The correction is being made on the mirror
lane and will be merged from main. Continue the other regions meanwhile.

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
