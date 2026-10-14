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
instrumentation-call terms (their equality is checked in Lean). Six
peer-get decision/exit regions are proved. The loop is not yet composed
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
