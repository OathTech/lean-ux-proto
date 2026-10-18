# Paired index insertion: execution report

Status: complete function and arbitrary finite mixed-sequence theorems build
on `task/binary-pair-runner`, from baseline `41675f86` under the
[charter](2026-10-18-charter-paired-index-insertion.md). Final fresh replay
and corrected capture regression pass; exact-commit export is being prepared.
The insertion increment's external export acceptance is pending.

Start: **2026-10-18 17:23:07 UTC**. Reassessment if incomplete:
**2026-10-19 17:23:07 UTC**. Supporting runtime optimization allowance: two
focused hours, zero used. No merge, push or changes to mirror/oracle/global state.

Mirror pin `cb2348e` now lags main `783510e850e187549cbb9380e53790e1ed232c77`.
Private Kraken is clean at `cd2ae360bfcf8e1fc719793405811ff49c3e75ce`,
Lean v4.35.0; approved s4 ELF SHA256
`16c346209885db6c610d4aa126c6eb30f5d3c02f0498d95e606473945f648774`.
The previous subsystem's external export gate passed on 2026-10-18 at
`fe596fd0b1d75a15801bf679657380676f61c0d6`: `PairSubsystemSurface` and its full
closure were accepted with only `propext`, `Quot.sound` and `Classical.choice`.
The independent trust-surface review is completed and dispositioned below.

Initial inspection confirms 109 insertion instructions. The common unlink
segment, finite bucket decoder and storage frames are reuse candidates.
The new service boundary is `get_random_u32`, whose wrapper calls the raw
entropy provider and `kcov_choice_ip`; input coupling must remain explicit and
must not assume arbitrary draws from a fixed deterministic machine state.

The start checkpoint had no insertion theorem or passing insertion test.
Current headlines are `Insert.insert_checked`, `Insert.insert_simulation`
and `InsertSequence.sequence_checked`; their conditions include the named
unproved service contracts and explicit sequential environment. The dated
sections below distinguish earlier partial stages from the current result.

## Independent review disposition

The [surface review](2026-10-18-review-paired-index-subsystem.md) permits the
insertion extension on the existing conditional sequential foundation. It
found no circular future-Pre/execution premise. Each finding is retained:

- **R1, medium, fixed for the extension:** the old sequence permission domain
  covers arbitrary prepared heaps. `InsertSequence.EntryDomain` restricts the
  *permission quantifier* to entries prepared from established `Ready` and
  source-admissible calls. Composition proves this domain at every call. This
  weakens the environment hypothesis, not the source domain or R. The prior
  exported theorem is unchanged.
- **R2, medium:** the old returning-history premise also covers histories that
  returned earlier and later reached the same boundary again. This is a stronger
  assumption, not a first-return safety result. The new headlines explicitly
  retain that broader premise; the reviewer permits documenting it until a
  first-boundary proof is available. It can include earlier returns followed by
  executed caller continuations. This is an applicability limitation, not an
  established exclusion of those continuations.
- Intermediate Ready was absent from the old exported per-call observation.
  The extension exports `SourceBoundaries`, the actual sequence of mirror
  postworlds, and a matched `Boundary` for each binary return. Each includes
  the full retained `Ready`, reconstruction, input cursor and actual history.
  The final postcondition therefore exposes correspondence at every return.

The interruption left only the review document uncommitted. It was preserved,
including that untracked file, at recovery ref
`refs/recovery/binary-pair-runner/20261018T172711Z`; branch HEAD was not changed
by preservation. No other worktree was modified. The preceding external export
was then accepted under the user's external command, as recorded above.


## Input and execution checkpoint, 2026-10-18 17:43 UTC

The independent `s2_index_collision` recording passes: one trace, four
operations, 29 operand pairs and 17 distinct operand rows. The new opt-in
`index-insert` profile names only `wg_index_hashtable_insert`, deriving its
range from the approved ELF; it changes no guest or kernel behavior. Literal
image/layout generation checks all 109 anchored instructions and their relative
branch encodings. The existing removal/replacement generated files are unchanged.

The paired supplied-service test passes the independent kernel-coverage and
mirror-decision comparisons for the two source-selected insertion calls. Across
two undefined-value seeds, five cases execute 36 retained-heap calls, 21,936
interpreted instructions and 128 input draws. Generated cases include 0, 1, 8
and 32 collision retries, nonempty same-bucket insertion, reinsertion and zero
as the accepted index. Four controls reject exhausted input, a wrong record
site, short payload and nonzero padding. The paired run took 3.760 seconds.

These are actual anchored, KCOV and BH instructions under Kraken, with an
explicit **supplied random-service return**. Neither `get_random_u32` nor its
entropy/recording callees execute under Kraken in this test. The runner reports
that boundary and does not count it as interpreted instructions. Its source is
the actual `WG.indexInsert`, including refusal behavior and exact input cursor.
All lookup reconstruction and owner-linkage assertions remain unchanged;
source environment records are separate from physical reconstruction.

A read-only sequential QEMU capture selects the second insertion of operation
1, after the first peer was inserted. It records 33,625,812 entry bytes at the
actual KCOV capacity of 4,194,304 words and reaches return after 1,354 native
instructions. Both random-service invocations return through their actual
bodies (511 instructions each), including the steered collision and fresh
value. Within the captured projection, their changes are stack and KCOV bytes.
Private entropy/recording state is not included in that projection. Segmented
Kraken replay against these boundary snapshots is running; **no passing
captured replay is claimed yet**. Applying a captured native service transition
is explicitly distinct from interpreting its instructions under Kraken.

`PairInsertInputProof.draw_hidden` proves that the tested input decoder consumes
the same bytes and leaves the same cursor as the actual mirror's `hiddenU64`.
Fresh kernel replay passes with only the three standard axioms. The first
pointer-effect components, `PairInsertMemory` and `PairInsertFields`, prove
exact chronological hlist stores, scalar frames and the newly linked node's
fields, reusing the old word-plan and storage-separation lemmas. They do not yet
prove whole-table reconstruction, source retry composition or function adequacy.
No new semantic hypothesis or axiom has been installed in `TrustBase.lean`.
The random-service contract and its compatibility with the input tape remain
an open trust-surface item before function composition.

Validation: default `capped lake build` passes (698 jobs before the last field
module); the insertion executable and all currently written local proofs build.
The harness/evaluator unit tier passes 72 tests, with one existing skip.
Initial development builds failed on syntax/elaboration and the literal fetch's
recursion limit, then passed after correction. The first runner failed noisily
because its decoded callback closure omitted `write_comp_data`; adding that
actual body fixed it. No killed build or timeout has occurred. Supporting
runtime optimization has still used zero focused hours. No completed fresh
function rate can be reported at this intermediate point.

## Reconstruction and capture checkpoint, 2026-10-18 18:05 UTC

The captured segmented replay now **passes**, for both undefined-value seeds.
Each run interprets 332 instructions and applies the two sampled native random
service transitions (1,022 native instructions, explicitly not interpreted).
Together these account for the capture's 1,354 instructions. It compares all
33,625,812 captured final bytes, 16 general registers and the represented flags,
and compares the captured service-entry memory/registers before each transition.
The result is 287454020, matching the mirror after one collision. At unchanged
KCOV capacity the replay took **5:53.82**, 350.26 CPU seconds and 10,438,732 KiB
maximum RSS. No runtime optimization was attempted. Reproduce with
`capped binary/.lake/build/bin/binary-pair-insert-capture
.tmp/binary-insert/input.json .tmp/cap-index-insert/snapshot.json
.tmp/cap-index-insert/layouts.json` after the capture command described by
`binary/capture_index_mutator.py --help`.

`PairInsertReconstruct.InsertFocus.reconstruct` now proves the combined
hlist-add stores restore the same executable relation at every bucket, while
retaining every owner peer word and peer count. The local chain and fuel bounds
are derived from the existing decoder and allocation-name validation. The source
bucket walk is connected to the landed mirror by a checked definitional equality;
its first-walk miss entails the second-walk miss under sequential execution.
Neither fact assumes the desired second walk or a future reconstructed state.
Whole-function instruction composition and the random-service contract remain
open; this checkpoint is not insertion adequacy.

A proof-cost issue was isolated: direct reduction of an unchanged field of
`target` evaluated the 8,192-bucket array before projecting the owner/count field.
Three slow development builds were stopped by their individually inspected owned
PIDs; a low-heartbeat diagnostic then failed in kernel checking. Those are failed
attempts, not successful validation. An explicit record-normalization lemma lets
projection rewriting avoid that reduction. With it, the entire reconstruction
module checks in 0.64 seconds under a diagnostic 3,000-heartbeat limit; its normal
build is under a second. The executable target and relation are unchanged. This
is proof-normalization reuse, not a measured improvement to captured replay.

`PairInsertSourceLoop.source_path` now extracts the finite retry path from every
accepted actual mirror insertion. `PairInsertSourceInput.source_input_effect`
derives the ordered collision/fresh-draw protocol, exact remaining input cursor
and updated index table. `hidden_draw` proves the runtime decoder's converse,
so accepted supplied mirror draws cannot escape its site/shape checks. These
proofs retain source refusal behavior and introduce no new trust premise.

The default build passes (706 jobs); the trust-gate unit tests pass. Fresh
kernel replay of `PairInsertReconstruct` and `PairInsertSource` passes, and the
new source-input closure also passes fresh replay. All printed local theorem axioms
are the three standard axioms. The external acceptance above remains scoped
to the preceding index subsystem, not these new insertion components.

## Retry frames and initial instruction regions, 2026-10-18 18:16 UTC

`PairInsertIndex` proves that every index overwrite on the unlinked resident
entry preserves whole-table reconstruction and supplies the fields required
by the eventual insertion. `PairInsertOwnership` proves that these overwrites
preserve owner linkage flags and that the combined insertion stores mark just
the inserted owner as linked, retaining all other flags. Both concern the
existing executable decoders; no reconstruction clause was weakened.

The nested BH-disable initially raised a potential gap in callback framing:
the old library covered two preempt-count phases and insertion uses three.
`PairInsertCoverage` proves that the two disabled phases have identical
instrumentation gates, metadata reads and coverage requirements under the
existing hardirq guards. Consequently the earlier physical footprint covers
the third phase too. No additional separation precondition was added. The
mask proof uses arithmetic lemmas and `omega`, with only standard axioms; no
native bit-vector axiom is used. Clearing irrelevant arithmetic hypotheses
and factoring modular division avoided a recursion-depth failure in an early
attempt, without retaining a raised recursion limit.

Fresh symbolic execution now covers the literal prologue, hashed-entry guard,
unlink predecessor/branch and clear regions. These are components, not the
whole-function result. Fresh kernel replay passes for `PairInsertIndex`,
`PairInsertCoverage` and `PairInsertRegions`; the default build passes. The
ownership closure also passes fresh replay. The input/reconstruction
checkpoint is commit `26efcbe5`.

Inspection of the native service histories confirms each sampled random call
actually executes `pushf`, `cli` and `sti`. These operations are absent from
the current Kraken model. The captured runner has therefore correctly kept
those service intervals native and explicitly labelled. A claim that this
capture already executes the complete helper under Kraken would be false.
The random-service contract/input coupling remains unresolved; its eventual
statement must not conceal this gap or promise arbitrary outputs from a fixed
machine state. No new service assumption has been installed yet.

## Nested-enable assertion finding, 2026-10-18 18:27 UTC

Deriving callback readiness exposed a missing conditional read in the insertion
entry assertion. For initial preempt count `0xfffffe00`, the outer BH-enable
does not read the pending-softirq word, but the nested enable does: its target
count wraps to zero. With pending word one, the original assertion accepted
the state and actual Kraken execution left the decoded function set at
`0xffffffff81073270`. The same wrapped count with pending word zero executed
to return. This was a failed readiness candidate, not a mirror discrepancy
or a completed theorem counterexample.

The tested assertion now checks the nested enable's exact conditional read and
separates that word from heap writes, scratch stack, coverage-buffer writes and
the preempt-count word. Wrapped counts remain accepted when these resources are
valid. The reconstruction relation and mirror are unchanged. The earlier
`nested_coverage` result remains valid: coverage metadata for the third phase
is already covered, whereas this additional BH-enable read was not.

The generated suite now passes six cases, two undefined-flag seeds and forty
calls. It includes positive wrapped-count execution through return and a
negative control rejected specifically by `insert.call.nested-pending-softirq`.
Reproduce after building `binary-pair-insert` by running it on the input prepared
by `binary/insert_probe.py`; the report names the generated wrap case and its
readiness control. This is generated entry evidence, not a captured kernel
state or a formal positive Pre witness.

## Walk-region reuse, 2026-10-18 18:30 UTC

Fresh instruction proofs cover the draw/index write and bucket-head load,
the two pointer-adjustment calls, both null-node guards and link advances,
all three BH-enable call sites, and the final index load/register restoration.
Direct repeated simplification of the second walk failed at the default
heartbeat limit. Factoring its test/jump and load/test/jump sequences into
parameterized effects, then identifying the literal image regions with those
sequences before simplification, makes the complete walk-region module check
in about one second. Failed elaborations' diagnostic axiom prints are not
validation; the successful module prints only the standard three axioms.
This is reusable instruction-effect reasoning, not full walk composition.
The default build passes (713 jobs).

## Three-phase callback resources, 2026-10-18 18:40 UTC

`boundary_frame` derives every physical callback-resource clause from the
tested entry assertion. `MemoryReady` carries the six saved registers, caller
return word, scratch mapping, coverage-buffer invariant, current preempt count
and both conditional pending-word reads. Its heap-write, callback, count-change
and CALL-slot preservation lemmas check. The existing two-phase coverage
machinery is reused through proved phase equalities; the extra pending read
has its own conditional separation proof.

The entry prologue and first coverage callback now compose into this invariant,
and the initial BH-disable/hashed-entry guard preserves it. Both walk comparison
branches also have checked effects. `IndexInsertDecoderAgreement` is the new
named declaration in `TrustBase.lean`: literal fetch agreement for the anchored
insertion instructions only. It asserts no callback behavior or input result.
The random-service assumptions remain open and are not silently installed.

The default build passes (720 jobs), and fresh kernel replay of
`PairInsertState`, including the resource-preservation closure, passes. Fresh
replay of the earlier walk-region module also passed. All new printed theorems
use only the standard three axioms. Full unlink/walk/retry/return composition,
formal positive Pre witnesses and the input-driven sequence theorem remain open.

[AGENT 2026-10-18] The insertion's internal shadow frame now compares only the
WireGuard storage cover, with saved-stack and callback resources carried
separately. Copying the earlier mutators' whole-memory equality outside their
small write footprint would incorrectly force the random provider's private
memory to remain unchanged. This is a proof-invariant adjustment; the executable
reconstruction and observation are unchanged. The shared storage-frame library
now supplies transitivity and protected-word reads. The initial composition and
unhash guard check against this frame. Fresh replay of their revised closure,
rooted at `PairInsertGuard`, passes. The default build passes with the two
additional callback/argument modules (722 jobs).

Equal protected stores now preserve the restricted shadow frame for both
32-bit index and 64-bit link writes. The resulting default build passes
(723 jobs). One development attempt at the 32-bit wrapper failed at the
heartbeat limit because its anonymous constructor's type was underconstrained;
an explicit `BitVec` type removed that elaboration search. No limit increase
or proof bypass was retained.

## Complete unhash prefix, 2026-10-18 18:54 UTC

`unhash_entry` now composes the actual prologue, initial callback, BH-disable,
both initial linkage branches and every nonempty unlink store/callback. Its
postcondition at insertion offset `0x4f` restores whole-table reconstruction,
owner linkage flags and the resident entry's fields, and proves its backlink
is zero. It rebases the internal shadow to the actual machine memory at this
correspondence point. It uses the existing named trace-PC and insertion-fetch
hypotheses; it assumes no later binary run or retry outcome.

This reuses the prior removal's chain/focus and combined-store reconstruction
lemmas. Fresh instruction/store composition and the entry adapter are specific
to insertion's register allocation and saved frame. The default build passes
(729 jobs), and fresh kernel replay of `PairInsertUnhashEntry` passes with only
standard printed axioms. This closes a function prefix, not insertion adequacy.

## Sequential flag support and capture regression, 2026-10-18 19:12 UTC

The private Kraken branch `task/binary-pair-insert-isa` now pins
`4651c92fa728734240de7ff4d5bdff3f05875806`. Its fifth reproducible patch adds
PUSHF, CLI and STI for 64-bit sequential execution. Non-arithmetic flags and
CPL are separate from arithmetic status; invalid PUSHF widths and denied
privilege fail explicitly. The pushed image clears RF/VM and reserved bits.
Interrupt delivery, the STI shadow and persistent RF remain outside the model.
The default CPL is unprivileged; captured kernel states explicitly load CPL 0.
No random-service contract has been added by this ISA extension.

Concrete instruction/parser tests and symbolic CLI/STI effects pass, with only
the standard three printed axioms. Fresh kernel replay of
`Kraken.X64.SystemFlagsTests` passes. The full consumer build passes at the new
pin (730 jobs). Initial test drafts failed because of two incorrect expected
flag masks and parser/test syntax; these were corrected, not counted as passes.

The captured insertion test now loads and compares the represented system
flags as well as the earlier six status flags. A negative control flipping IF
is rejected specifically by that comparison. The unchanged actual capture
passes for both undefined-value seeds: 33,625,812 compared bytes per run,
332 interpreted anchor/callback instructions and 1,022 sampled native random
instructions, 1,354 total. The random body remains a labelled sampled transition
in this capture test. Repeating the previously documented capture replay command
took 5:51.51 elapsed, 347.60 user CPU seconds and 10,438,404 KiB maximum RSS.
The supporting runtime-optimization budget remains unused.

## First retry boundary and cached-provider execution, 2026-10-18 19:14 UTC

`Core.enable_region` is shared by all three BH-enable sites. Its nested case
uses the conditional pending-word resource established by the tested assertion.
`retry_entry` composes the complete unlink prefix, its final callback, initial
BH-enable and new BH-disable to insertion offset `0x6f`. Reconstruction,
ownership and the resident unlinked entry are restored there for both initial
linkage cases. `RetryData.frame` carries these data facts through service-only
segments. Fresh replay of `PairInsertEnable` and `PairInsertPrefix` passes;
the printed theorems use only the standard three axioms. The full build passes
(736 jobs). Development errors were local elaboration/normalization issues;
new unused simplification arguments were removed rather than suppressed.

The separate `binary-pair-random-body` executable now runs the actual decoded
cached random-provider body and its callbacks, with recording disabled and
explicitly synthetic private memory. Eight runs pass: two retained-cache calls,
two initial IF values and two undefined-value seeds. They return 7 and 8199,
clear the consumed words, advance the position and restore the caller's IF and
callee-saved registers. Each call executes 233 instructions with IF initially
clear or 245 with IF set. A CPL-3 control fails at the actual CLI instruction.
Reproduce with `capped lake build binary-pair-random-body` in `binary/`, then
`capped binary/.lake/build/bin/binary-pair-random-body` from the worktree root.

`generate_random_service.py` reproduces the partial random/recording decoder
from the pinned ELF and checks direct-branch encodings. Unsupported instructions
and absent callees remain failing fetches. This is positive execution evidence
for the cached path, not a general random-provider theorem or the formal
insertion Pre witness. The refill path contains REP STOS, still unsupported;
the arbitrary accepted-retry theorem must not be narrowed to the cache size.
No random-service assumption has been installed while its physical domain and
recorded-input coupling are unresolved.

## Shared bucket-loop composition, 2026-10-18 19:24 UTC

`walk_chain` composes both actual compiled bucket walks using one induction on
the finite chain extracted by reconstruction. It returns the exact collision
or miss endpoint, preserving the storage relation, coverage/stack resources
and the live query registers. The second walk additionally preserves the
bucket-number register. There is no bucket-length or execution-fuel bound in
this theorem. Existing executable names validation supplies the non-NULL,
non-wrapping owner facts; no new entry restriction was introduced.

The shared node step handles the pointer adjustment, guard, instrumentation,
comparison and advance. These are actual decoder-agreed instruction histories,
not an abstract replacement for execution. The two sites differ by a code
offset and compared-value register. The complete walk module is 72 lines; its
new data, site, branch and node support is 354 lines. This is reuse within this
increment, not a measurement of campaign-wide throughput.

The targeted build and fresh `capped lake env leanchecker PairInsertWalk`
replay pass; printed axioms are the standard three. The default build passes
(741 jobs). Failed draft elaborations were word-normalization and Boolean
orientation issues, corrected before replay. Insertion adequacy and the
random-service contract remain open.

## Nested recheck entry, 2026-10-18 19:32 UTC

`nested_entry` now executes the second BH-disable, reloads the resident index,
computes its bucket and reaches the shared locked walk with the same storage
relation. The preempt-count transition preserves the saved frame, coverage and
both conditional pending-word resources. `RetryData.draw` proves that updating
an unlinked owner's index preserves reconstruction and ownership and leaves
the resident allocation ready for a later retry.

The fresh seven-instruction symbolic block repeatedly exhausted the default
200,000-heartbeat limit; a local 1,000,000-heartbeat attempt also failed. These
are failed builds. Splitting the block into count, load, mask, head-load and
test effects made the physical module elaborate in about one second, with no
raised heartbeat limit retained. This is a concrete symbolic-execution cost
and a useful local remedy; cuts remain proof choices. The existing generic
test-branch lemma is reused for the final guard. The reconstructed read and
separation facts discharge all the physical loads at composition.

Targeted builds and fresh kernel replay of `PairInsertNested` pass, with only
the standard three printed axioms. The default build passes (745 jobs).

## Draw, search and prepend, 2026-10-18 19:39 UTC

`draw_entry` consumes the actual low 32 bits returned in RAX, writes the
unlinked owner and supplies a reconstructed insertion focus. It makes no
recorded-value assumption. `search` then composes the complete first walk and,
on a miss, the nested recheck. The second miss follows from the unchanged
chain. `InsertFocus.collision` identifies the physical walk's result with the
mirror table's index-membership test. A collision reaches the retry point;
a miss reaches the prepend stores with the bucket register and heap relation.

`prepend` executes all three initial stores, the old-head repair when needed,
and the real intervening callbacks. Its post-state uses the same combined
`insertMemory` definition tested by the runner and covered by reconstruction
and ownership lemmas. The new store wrappers share a register-to-memory store
lemma; the guard reuses the earlier test lemma. Mappedness after stores is
reused directly rather than reproved by a disjointness argument.

Fresh replay of `PairInsertPrepend` passes, including its imported search and
draw modules. Printed axioms are the standard three; the full build passes
(751 jobs), with no warnings in these new modules. One draft generic-store
adapter timed out; its single literal instruction is now reduced directly.
Other draft failures were local normalization and rewrite mismatches. The
return composition and honest random-service boundary are still open.

## Successful suffix to return, 2026-10-18 19:41 UTC

`insert_success` composes prepend, both BH-enable calls and the actual register
restore/RET. It exports the returned index, restored caller ABI, preempt count,
coverage and pending-word resources, reconstruction of the inserted table and
ownership. Its entry is the successful-search correspondence point; it is
not yet the function-level theorem. Fresh `leanchecker PairInsertSuccess`
replay passes and its axioms are the standard three. The default build passes
(753 jobs). No new trust assumption was introduced for this suffix.

## Random-provider refill execution, 2026-10-18 19:52 UTC

The decoded random body now includes initialized refill and generation-refresh
paths. Synthetic private memory, with recording disabled, executes an ordinary
refill in 5,580 instructions and a changed-generation refill in 8,151; each is
followed by a retained-cache call of 245 instructions. The earlier eight cached
runs still pass. The checks cover the return stack, callee-saved registers,
CPL/IF, cache generation, position and consumed-word clearing. The unprivileged
CLI control still fails at the expected instruction. These are actual Kraken
body executions, not supplied returns, and remain distinct from kernel captures.

Execution found REP STOS and JG missing from Kraken, plus a three-byte NOP
spelling in the generated decoder. Private Kraken commit
`05bd93e14ab946330004a57403accc135c7e5542`, reproduced by patch 0006, implements
64-bit-address STOS with all operand widths, DF and per-element permission
requests, and the signed greater condition. Other STOS address modes explicitly
fail. Separate instruction tests and fresh kernel replays pass. The consumer's
generic memory-invariant theorem needed a structural induction for repeated
stores; its first full build failed on that missing case, which is now fixed.
No failed build is counted as validation. The default regression build is
pending at this checkpoint.

`generate_random_service.py` now includes ChaCha and memcpy's literal ELF
implementation. It translates only the exact `0f1f00` memory-shaped NOP encoding
to Kraken's existing three-byte NOP. Boot-patched alternative implementations
of memcpy are not covered by this literal decoder. The body probe is evidence
for a service domain permitting refills; it is not a general provider theorem,
an insertion Pre witness, or evidence that captured steering state is covered.
The new random-service contract and recorded-input agreement remain open.

## Physical frames and system state, 2026-10-18 19:59 UTC

[AGENT 2026-10-18] Carry the ordinary-region write footprint separately from
reconstruction. Provider readiness must survive intervening bucket walks and
unlink stores; equality on represented WireGuard storage alone cannot establish
that. `Core.outside` relates the shadow heap and actual heap outside stack,
coverage and preempt-count writes. Shadow stores still follow the combined
pointer effects. This is a physical frame, not a stronger observable relation.
The random-service step may rebase the shadow to its returned private state.

The entry/unhash prefix and successful insertion suffix now export their
write footprints and immutable owner-tag frames. Fresh kernel replays of
`PairInsertPrefix` and `PairInsertSuccess` pass. `SystemInvariant.eventually_mode`
separately proves CPL and DF preservation from every implemented instruction,
including REP STOS; service executions inherit it without another contract
premise. Its fresh replay passes and all printed axioms are standard.
The stable-tree default build passes (754 jobs), completing the regression
check for the refill ISA extension as well as the frame changes.

One regression run failed with missing `.olean` files because overlapping
builds coincided with a dependency edit. That run is a failure, not evidence;
validation was rerun after the tree stabilized. The first generic system-state
proof exhausted 200,000 heartbeats. Handling CLI/STI and the memory/register
CMPXCHG cases explicitly reduced elaboration to about five seconds without a
raised heartbeat limit. Routine draft namespace errors were also corrected.

## Executable provider domain, 2026-10-18 20:04 UTC

`RandomProvider.check` now checks initialized entropy/cache allocations and,
when recording is active, the selected steering graph. It first reads a
declared finite private allocation cover; a proved frame lemma therefore
preserves the whole executable check when those bytes are unchanged. The
cover's separation from WireGuard storage remains a physical entry obligation.
Remote-node traversal is bounded by a finite allocation interpretation, with
cycle rejection; that bound does not constrain collision retries or draws.

`generate_random_layout.py` derives KCOV structure offsets/sizes and provider
symbols from the pinned ELF. The private check passes before and after all
eight cached runs and four refill/retained-cache runs. Removing a cache byte
is rejected as unmapped. `RandomStateFrame` passes fresh kernel replay, using
only standard axioms. Active recording/steering execution is still outstanding;
its actual copy branch reaches REP MOVSB, the next private ISA extension.

The draft `RandomReturnContract` is now named in `TrustBase.lean`, together with
its physical `RandomReady` and write footprint. It promises an actual service
return, preserved physical provider/coverage/BH resources and IF, but no selected
random value. It is an explicit unproved hypothesis, not an asserted axiom,
and no insertion headline uses it yet. Its full entry-domain witness and
active-recording tests remain due. Recorded-input agreement remains a separate
open safety premise; there is still no full insertion theorem or export claim.

## Recording-enabled provider and complete capture replay, 2026-10-18 20:35 UTC

The paired capture now executes the random body under Kraken. The capture
helper reads the initialized provider allocations and selected direct/remote
steering graph from the stopped kernel; no private bytes come from expected
mirror values. This selected capture uses direct steering. The standalone
synthetic suite additionally exercises the remote graph, steering exhaustion,
ordinary refill and changed-generation refill. All 18 provider cases pass
the complete executable `readyCheck`, return/ABI, coverage/preempt, private
readiness, IF and endpoint-footprint checks. Controls reject a missing private
byte, unprivileged CLI, a missing stack byte, private/stack aliasing, DF set,
and an endpoint write outside the contract footprint.

Private Kraken commit `cd2ae360bfcf8e1fc719793405811ff49c3e75ce` adds MOVS and
memory XADD; patch 0007 reproduces it. MOVS follows per-element access order,
including overlapping copies, all widths and both directions, with 64-bit
addressing. XADD freezes the effective address before overwriting its source
register, updates arithmetic flags, and requests both memory permissions.
Register XADD and LOCK remain unsupported. Instruction tests, fresh kernel
replay, and consumer memory/system preservation proofs pass. The stable
default regression after the ISA extension passed 759 jobs.

The first full captured-body replay failed the PC-sequence check. Diagnosis
found 503 Kraken instructions versus 511 native stops in each random call:
QEMU single-stepping exposes each REP iteration, whereas one Kraken instruction
executes the whole repeat. The runtime now validates each native multiplicity
against actual entry RCX, including zero-count behavior, before comparing
the instruction sequence. This changes test granularity, not ISA execution
or the endpoint comparison. A reduced-memory diagnostic also failed its
endpoint check because its two truncated buffer spans had different lengths;
that diagnostic was not a passing capture result.

The corrected full replay passes both seeds. All **1,338 interpreted
instructions** execute under Kraken, including both random calls; the native
trace has **1,354 single-step stops**. Each seed compares **33,626,364 bytes**,
all checked endpoint registers/status/system flags, the recorded draws
`0x0a0b0c0d` and `0x11223344`, the mirror result, decisions and coverage. The
KCOV capacity remains **4,194,304 words**. No sampled native service transition
is installed. Reproduction uses the existing independent recording and:

```sh
LEANUX_QEMU_SLOTS=16 capped scripts/in-bundle /usr/bin/python3 -B \
  binary/capture_index_mutator.py --anchor insert --call-index 1 \
  --input .tmp/binary-insert/input.json --check .artifacts/check/binary-insert \
  --operation 1 --out .tmp/cap-index-insert-private
capped binary/.lake/build/bin/binary-pair-insert-capture \
  .tmp/binary-insert/input.json .tmp/cap-index-insert-private/snapshot.json \
  .tmp/cap-index-insert-private/layouts.json
```

The full replay took **9m47.70s elapsed**, **583.45s user CPU**, and
**11,312,384 KiB maximum RSS**. It repeats large mappedness and endpoint
comparisons; this is a measured remaining runtime cost. No time has been
spent on the separately budgeted capture optimization experiment. The
capture remains the sequential/no-IRQ baseline, and the refill executions
remain synthetic rather than captured refill evidence.

## Physical and input service composition, 2026-10-18 20:35 UTC

[AGENT 2026-10-18] Use a separate input-coupling safety specification instead
of making the physical return contract prescribe arbitrary draws. The named
`RandomInputCoupling` takes an external input interpretation of private memory
and remaining records. It is stable under equality of provider-private bytes.
At a fixed coverage/preempt context and return address, with current physical
readiness and the entry frame established, its law constrains an existing
actual service history: the low 32-bit result equals the next decoded record
and the interpretation advances. It asserts neither execution existence nor physical
readiness, a future insertion result, or reconstruction. The interpretation
and coupling remain explicit environmental hypotheses, not proved facts about
arbitrary recordings.

`RandomService.return_recorded` composes that safety law with the separately
named physical `RandomReturnContract`. Its actual histories come from the
service execution proof. Mappedness, CPL and DF preservation are derived from
the ISA, rather than added to the contract. `RandomService.Post.ready` restores
the same physical reservation over the returned heap. `RandomReadyCheck` proves
that the complete runtime readiness assertion establishes `RandomReady`.

Insertion's `providerCheck` and `ProviderFacts` supply the larger stack
reservation and separation of private allocations from represented storage,
caller frame, callback state and conditionally read pending words. Their
initial-call capture check remains to be wired into the runner; the captured
random-service entries already pass `readyCheck`. `ProviderState.follow`
carries private readiness through ordinary regions, using their footprints
and generic ISA invariants. `Core.random_ready` derives service readiness
after the actual CALL push. `Core.random_memory` preserves saved words,
coverage, preempt and both conditional pending resources; `Core.random_call`
composes the actual CALL, physical return, recorded-value agreement and
reestablished caller invariant. These targeted builds print only standard
axioms. Full insertion retry induction, function-level Pre/witness/adequacy,
retained-heap sequence extension and the increment export remain open.

Draft failures in this stage included Lean record/branch layout, a reserved
identifier, missing library lemma names and conversion recursion limits.
Explicitly reducing the two coverage-predicate definitions resolved the
conversion cases without raising limits. They were failed builds and were
corrected before the passing checks; no holes or bypasses were retained.

Review of the first coupling draft found its quantification too broad: it had
not fixed the recording context or caller return site. Those can change a
steered result while leaving all provider-private bytes unchanged. The
declaration now fixes both and requires current `RandomReady`/`EntryFrame`
premises. Executable controls pass: the same provider-private bytes return
steered value 41 at the selected recording site, but raw value 7 with recording
disabled or at another return site. A trace missing REP iteration stops is
also rejected. The subsequent full regression exposed a missing `MirrorLoop`
import after the input parser was made independent of the mutator library;
that failed build was repaired. The complete regression passes **769 jobs**,
and fresh Lean kernel replay of `PairInsertRandomCall` and its dependencies
passes. These checks establish the service-composition checkpoint; they do
not establish the still-open complete insertion theorem.

## Retry and complete-function composition, 2026-10-18 20:48 UTC

`retry_draw` composes the retry trace callback and random CALL. `draw_attempt`
then executes the index store, first chain scan, derived locked recheck and
successful prepend/return suffix, or restores the retry invariant after a
collision. The same physical/private frames carry the external input
interpretation through ordinary instructions. `retry_loop` inducts over
`Source.DrawSearch`, extracted from the actual accepted mirror execution;
there is no separate fixed binary retry budget.

`insert_checked` now builds and passes fresh kernel replay. It connects the
entry/unhash proof to that loop, including reinsertion, and exports return
value/ABI, reconstruction, ownership, callback resources, provider readiness,
remaining input and write/kind frames. Printed axioms are the standard three.
The named callback, physical random-return and input-coupling hypotheses
remain explicit. The serialized/access wrapper also builds; it retains the documented R2
return-history permission premise. Concrete formal entry witnesses and the
retained-heap sequence extension are not yet complete.

The capture runner now invokes the exact larger `providerCheck` at insertion
entry. Its complete-body rerun is in progress. Synthetic linked/unlinked Lean
witness states also include initialized private provider memory; their actual
body execution and kernel-checked Pre proofs are in progress. No new Pre is
being committed without its positive witness. Draft composition failures
were Boolean simplification and union-footprint composition; both were fixed
without changing the statements. One witness draft build was deliberately
interrupted after identifying an unsuitable finite-case tactic; it was a
failed attempt, not a passing check.

The complete captured-body rerun with `providerCheck` at insertion entry
passes both undefined-value seeds: 1,338 Kraken instructions against 1,354
native stops, checking 33,626,364 captured bytes per seed. Elapsed time was
10 min 52.15 s, CPU 648.17 s and peak RSS 11,315,184 KiB. Synthetic exact Lean
witness states also pass actual-body execution to return: 409 instructions
unlinked and 434 linked, each with seeds zero and maximum UInt64. An initial
fixture failure used the default CPL3; setting the synthetic state to CPL0
fixed the fixture, without changing Pre.

Formal witness normalization remains a cost finding. Several draft reductions
were deliberately interrupted after rapid memory growth; one diagnostic hit
the 32 GiB cap and exited 137 with a KILLED banner. These are failed attempts.
Abstract byte-list read lemmas avoid expanding the 64 KiB initialized table;
scalar checks and symbolic stack mapping compile separately. The assembled
entry witness is still being localized and checked. No failed draft is counted
as acceptance, and no new Pre is committed without the positive formal witness.

## Function and positive-witness checkpoint, 2026-10-18 21:23 UTC

`PairInsertWitness.check` now proves the exact executable Pre for both the
unlinked and linked synthetic states. `source_success` proves their actual
mirror executions return index seven, and `executes` instantiates the general
binary theorem with these states. The physical provider and recorded-input
contracts remain explicit; this is not a proof of those contracts.

The witness cost had two separate causes. Bare reflexivity on the argument
register equality caused explosive reduction even with abstract memory;
explicit state-projection simplification reduced that check to under a second.
Direct evaluation of the private snapshot checker also failed to reduce.
`provider_snapshot` and `provider_image_load` instead use the existing union
and byte-array lookup lemmas, then check the small scalar/list computations.
The provider witness builds in about 3.2 seconds, the assembled Pre in about
0.8 seconds, and the source/execution witness in about 0.8 seconds; the separate
byte/stack facts module took about 10 seconds. These are module build times,
not a fresh-function throughput estimate. The completed witness declarations
print only the standard three axioms. No Pre or reconstruction clause changed
to avoid a valid path.

`ProviderFacts.checked` also reassembles the runtime provider assertion from
its present-state fields; it is available for retained-heap caller composition.
The default regression passes **782 jobs**, and the six binary trust-gate unit
tests pass. An initial fresh-replay command supplied two modules together;
`leanchecker --fresh` rejected that invocation. Separate fresh kernel replays
of `PairInsertWitnessExecution` and `PairInsertEnvironment` both pass. The insertion external export gate is still outstanding.

The witness executable checks the image-derived layout against the declared
witness layout, evaluates both assertions using the formal witness context,
and runs those same states through the actual decoded provider and insertion
bodies. Reproduce from the worktree root:

```sh
(cd binary && capped lake build binary-pair-insert-witness PairInsertWitnessExecution)
capped binary/.lake/build/bin/binary-pair-insert-witness .tmp/binary-insert/input.json
(cd binary && capped lake env leanchecker --fresh PairInsertWitnessExecution)
(cd binary && capped lake env leanchecker --fresh PairInsertEnvironment)
```

This reaches the individual-function checkpoint; extended mixed finite
sequences, their retained-input invariant, final trust-surface refresh and
exact-commit export remain open. The scientific evidence supports testing the
same assertions that the proof uses, while this witness episode demonstrates
that proof-engine reduction costs are a separate expense that testing alone
does not remove.

At **21:25:33 UTC**, the complete function/witness checkpoint passed, **4 h
2 min 26 s** after the increment start. The exact-context witness rerun passed
all four executions (409/434 instructions, both seeds), and the private Kraken
tree is clean at the pin above. The remaining goal is still active: this is
not the retained-heap sequence or external-export completion point.

## Mixed-call invariant discovery, 2026-10-18 21:34 UTC

The four independent function comparisons pass again before mixed execution;
the existing eight sequences also pass (80 calls, 21,268 instructions,
3.155 seconds). The insertion comparison passes all six supplied-service
cases in 4.006 seconds. The new suite retains the initial provider allocations
and complete draw tape across all four anchors, including reinsertion.

Its first failure was a fixture encoding error: the kernel steering record
kind is 104, while the mirror index-draw site identifier is 4. The draw
comparison rejected the unsteered result. The fixture now uses the kernel
kind. The first driver draft also failed to display captured stderr; that
reporting defect was fixed so the diagnostic is explicit.

The next failure is a specification finding: with coverage capacity four,
Kraken reaches `kcov_choice_write_area` at `0xffffffff810f2615`, which reads
and increments `task_struct.kcov_leanux_dropped` at task offset `0x708`. The
old private readiness check accepted a state with that word unmapped and
omitted it from the declared private write cover. Thus the physical return
contract had an insufficient readiness domain; the checked conditional
insertion theorem did not prove that contract and must not be presented as
having settled it. The failure is a binary-resource specification defect,
not evidence of a new mirror discrepancy.

The correction derives the field offset from DWARF, checks its mapping in
active recording states, captures its actual bytes, and includes it in the
private cover. The complete 786-job build passes. The random-body suite passes
the saturated increment and rejection of an omitted allocation. No peer state
or observation is excluded. This is direct
evidence for the test-first invariant-discovery method, and a reminder that
successful non-saturating captures did not establish callback adequacy.

At **21:39:57 UTC**, the mixed runner passes **24 sequences, 312 calls and
382,224 Kraken instructions in 49.185 seconds**. Cases combine 1, 8 and 32
collision retries, live/dead first peers, ordinary/saturated coverage buffers
and both undefined-value seeds. Each sequence retains one allocation
interpretation, heap and private input-provider state across all thirteen
calls. These are labelled synthetic sequences derived from a recorded prefix,
not captured uninterrupted kernel execution. The arbitrary finite-sequence
proof was still in progress at that test checkpoint; runtime success was not
counted as its completion.

A fresh native insertion capture includes the formerly omitted four bytes
(33,626,368 entry bytes total; 1,354 native instruction stops). Its complete
Kraken replay passes for both seeds: 1,338 interpreted instructions, including
both actual random bodies, with native REP multiplicities checked separately.
All captured endpoint bytes, registers, represented flags, independent draws,
result and decisions agree. The corrected replay took **10m10.23s elapsed**,
**606.30s user CPU**, **3.84s system CPU**, and **11,316,396 KiB maximum RSS**,
exit zero. Actual KCOV capacity remains 4,194,304 words. The earlier capture's
success is not substituted for validation of the corrected readiness check.

## General mixed composition and scientific checkpoint

At **21:45 UTC**, **4h22m** after the increment began, the general finite mixed
theorem compiled. Its final, stronger public postcondition also compiles:
`InsertSequence.sequence_checked` produces actual per-call instruction
histories matched to an exact `SourceBoundaries` trace of the actual mirror.
Every return exposes `Ready`, including reconstruction, owner linkage, mapped
resources, the restored preempt count, coverage/pending state, initialized
private provider state and the exact remaining supplied input. The source
worlds are derived by the accepted calls, not independently chosen snapshots.

The existing three function proofs are reused unchanged. Their physical
write frames preserve provider-private bytes; a source frame proves they do
not consume the random tape. Insertion's postcondition supplies the changed
provider/tape. Explicit caller installation preserves both, and the next
insertion Pre is assembled from retained fields and static geometry. The
wide reservation implies the smaller nested callback's separation check;
there is no additional future-Pre or successful-future-execution premise.
One fixed Names interpretation and actual returned memory are used throughout.

The complete **793-job default build**, **four capture unit tests**, **six
trust-gate unit tests**, and **binary proof gate** pass. The gate prints and
diffs the expanded headline/definition specification and full named trust
declarations and requires the clean pinned Kraken tree. Fresh kernel replay
of **`PairInsertionSurface` and its transitive closure** passes, including
all insertion and mixed-sequence headlines and the linked/unlinked witnesses.
Every printed headline/witness axiom set contains only `propext`,
`Classical.choice` and `Quot.sound`. The exact witness executable was rebuilt
against the corrected definitions and passes all four entry-to-return runs.
The external export gate remains separate and pending for this increment.

The final mixed suite additionally exercises original preempt count
`0xfffffe00`, where insertion's nested enable reads the pending word while
the outer enable does not. It passes **32 sequences, 416 calls and 434,064
interpreted instructions in 58.302 seconds**. Controls reject a missing input
tape, provider/output aliasing, and a nonzero nested pending word when read;
each requires the intended diagnostic. These tests use the same initial and
retained assertions as the proof. No wrapped count or dead-peer state was
excluded to make the composition close.

The measured marginal result is **one 109-instruction anchored function plus
its four-function finite composition in about 4h22m to the first general
composition build**, followed by final validation. As a descriptive quotient
this is about **25 anchored instructions/hour** or **0.23 functions/hour**.
It is not a campaign throughput estimate: it includes capture/invariant
discovery, service execution work, witnesses and composition, reuses a large
existing foundation, and leaves universal service contracts as hypotheses.
The more than one thousand random-service instructions executed in tests are
not additional proved function coverage.

Relative to `41675f86`, the current increment adds **10,066 Lean lines and
removes three**, across 107 Lean files; **1,610 added lines are generated
instruction/layout declarations**. The total includes executable runners and
witnesses, not just proof terms. Mixed composition, its source-input frame and
runner account for 1,026 lines. These counts describe engineering volume,
not interchangeable proof obligations. The full pointer effects, bucket walks,
retry and physical-service resource work occupy most of the new material;
the last finite-list composition reuses those results.

The scientific result is stronger than a runnable paired test. Testing
rejected incomplete invariants (the nested pending word and saturated
recording counter), and the corrected executable assertions are the definitions
used by the general proof. Structural mutation, retries and retained-state
composition now work within the declared sequential domain. This supports
the method's feasibility and shows reuse at composition. It does **not** yet
establish affordable campaign-wide scaling. Proof normalization, concrete
memory reduction, callback resources and trust reduction remain real costs;
the slow witness attempts, interrupted builds and one killed build above are
part of that cost, not passing evidence. No supporting capture optimization
budget was used.

### What this result does not establish

- Concurrent contextual refinement, interrupts/preemption between internal
  points, or environmental execution at BH-enable boundaries. The environment
  is explicitly serialized; the captured baseline follows that restriction.
- Allocation, freeing, RCU transitions, allocation-identity reuse, or compiled
  caller execution. Allocation names are fixed and caller setup is explicit.
- The whole WireGuard world, complete operations/traces, or transport of the
  landed campaign properties. This is the index projection and its interfaces.
- Termination for every possible draw stream or correctness of source-refused
  cases. The result covers arbitrary finite accepted mirror executions;
  exhausted/malformed input and refcount saturation remain explicit refusals.
- Universal image proofs of the five callback contracts or
  `RandomReturnContract`, or a proved recorded-stream `RandomInputCoupling`.
  Actual-body tests constrain those specifications but do not discharge them.
- Real kernel-entry reachability or a realism theorem for all Pre states.
  Concrete formal witnesses establish non-vacuity and execute to return.
  Capture tests reconstruct the source input from actual entry bytes; they do
  not prove that the workload's mirror prefix reaches that captured state.
- Equality between generated mixed sequences and uninterrupted native kernel
  executions. Their origin is labelled; only the separate actual capture has
  independently captured entry and return bytes.
- First-return permission safety. R1 is repaired in the new permission domain;
  R2's broader returning-history premise remains explicitly assumed.
- External kernel acceptance for this new export before the user's result.
  The accepted previous subsystem export covers its stated earlier commit.

## Named trust base at the composition checkpoint (verbatim)

The following is `binary/TrustBase.lean`, including the older sibling surfaces
that share this module. Only premises appearing in the printed insertion and
sequence headlines are hypotheses of those results. No declaration here is a
project axiom; the service specifications remain explicit theorem hypotheses.

```lean
import FiniteExecution
import Image
import IndexMutatorImage
import IndexInsertImage
import AllowedipsImage
import ServiceImage
import Memory
import LookupProjection
import AllowedipsProjection
import AllowedipsSelection
import AllowedipsWords
import RandomState
import PairInsertInput

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

def krakenCommit : String := "cd2ae360bfcf8e1fc719793405811ff49c3e75ce"
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

/-- Sequential paired removal uses the same pinned ELF interpretation, with
its separately generated literal instruction range. -/
def IndexRemoveDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, IndexMutatorImage.Remove.fetch pc = some instruction → fetch pc = some instruction

/-- The separately generated replacement range of the same pinned ELF. -/
def IndexReplaceDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, IndexMutatorImage.Replace.fetch pc = some instruction → fetch pc = some instruction

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

/-- External access safety for actual finite histories completing this ABI
call, including service interiors. It asserts no run exists, no source
result, and no reconstruction. The unexecuted caller continuation is omitted.
This form also covers a function that tail-calls its returning service. -/
def ReturningCallPermissions (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (initial : MachineState) (returnAddress : UInt64) : Prop :=
  ∀ history final, ActualHistory fetch initial history → history.getLast?=some final →
    Returned initial final returnAddress → RunAccessAllowed fetch permissions history

/-- The same explicit permission premise for a family of caller-prepared
entries. It grants access on actual returning histories; it neither asserts
their existence nor supplies any future reconstruction or precondition. -/
def ReturningDomainPermissions (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (returnAddress : UInt64) (domain : MachineState → Prop) : Prop :=
  ∀ initial, domain initial → ReturningCallPermissions fetch permissions initial returnAddress

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
  | pc | cmp1 | cmp4 | cmp8 | constCmp4 | constCmp1
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

/-- KCOV comparison record encoding: width in bits 1..2, constant bit 0. -/
def KcovRecordTag : KcovKind → BitVec 64
  | .pc => 0 | .cmp1 => 0 | .cmp4 => 4 | .cmp8 => 6
  | .constCmp4 => 5 | .constCmp1 => 1

/-- Callback argument width is fixed by the called entry point. -/
def KcovArgument (kind : KcovKind) (s : MachineState) (reg : Reg64) : BitVec 64 :=
  if kind = .constCmp1 ∨ kind = .cmp1 then (s.data.regs.get (.low reg .W8)).setWidth 64
  else if kind = .cmp8 then s.data.regs.get64 reg
  else (s.data.regs.get (.low reg .W32)).setWidth 64

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
    let tag := KcovRecordTag kind
    let arg1 := KcovArgument kind s .rdi
    let arg2 := KcovArgument kind s .rsi
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

/-- Additional anchored decoder domain for M2; M1 agreement is separate
    because peer-get is shared. The linked-label interpretation is unchanged. -/
def AllowedipsDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, AllowedipsImage.fetch pc = some instruction → fetch pc = some instruction

/-- A callback's interior is not another anchored M2 invocation. -/
def NoAllowedipsReentry (history : List MachineState) : Prop :=
  ∀ s ∈ history.dropLast, AllowedipsImage.fetch s.pc = none

/-- M2 uses the same physical callback specification, with its additional
    anchored ranges excluded from callback interiors. The original M1
    contracts and their hypotheses remain unchanged. -/
def AllowedipsServiceReturns (fetch : Int64 → Option Decoded) (address : Int64)
    (ready : MachineState → Prop) (writes : MachineState → BitVec 64 → Prop)
    (effect : MachineState → MachineState → Prop) : Prop :=
  ∀ s returnAddress, s.pc = address → ready s → EntryFrame s returnAddress →
    Eventually (historyStep fetch)
      (fun t => Returned s t.machine returnAddress ∧
        EqualOutside (writes s) s.data.dmem t.machine.data.dmem ∧
        effect s t.machine ∧ NoAnchoredReentry t.history ∧ NoAllowedipsReentry t.history)
      ⟨s, [s]⟩

def AllowedipsTracePcContract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810f3100)
    (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)

def AllowedipsTraceCmp1Contract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810f3e40)
    (KcovReady .cmp1) (KcovWrites .cmp1) (KcovEffect .cmp1)

def AllowedipsTraceCmp8Contract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810f3ea0)
    (KcovReady .cmp8) (KcovWrites .cmp8) (KcovEffect .cmp8)

def AllowedipsTraceConstCmp1Contract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810f3ec0)
    (KcovReady .constCmp1) (KcovWrites .constCmp1) (KcovEffect .constCmp1)

def AllowedipsTraceConstCmp4Contract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810f3f00)
    (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4)

/-- As in M1, this contract covers the no-pending-work BH-enable path.
    M2's Pre must justify the actual read conditions and stack separation. -/
def AllowedipsBhEnableContract (fetch : Int64 → Option Decoded) : Prop :=
  AllowedipsServiceReturns fetch (.ofNat 0xffffffff810732c0) BhEnableReady
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


/-- M2 calls PC and comparison instrumentation in both BH phases. Buffer
    metadata is required only when the physical callback reads it. -/
def AllowedipsCoverageNeeded (coverage : KcovLayout) (preempt : BitVec 32) : Prop :=
  LookupModeRead coverage preempt ∧ (coverage.mode = 2 ∨ coverage.mode = 3)

def AllowedipsCoverageAt (coverage : KcovLayout) (preempt : BitVec 32) (memory : Mem 64) : Prop :=
  load64 memory currentTaskAddress = some coverage.task ∧
  (LookupSoftRead preempt → load32 memory (coverage.task+0x704) = some coverage.softirqEnabled) ∧
  (LookupModeRead coverage preempt → load32 memory (coverage.task+0x6e0) = some coverage.mode) ∧
  (AllowedipsCoverageNeeded coverage preempt →
    load32 memory (coverage.task+0x6e4) = some coverage.capacity ∧
    load64 memory (coverage.task+0x6e8) = some coverage.area ∧ KcovBuffer coverage memory)

def AllowedipsCoverageWrites (coverage : KcovLayout) (preempt : BitVec 32)
    (a : BitVec 64) : Prop :=
  (AllowedipsCoverageNeeded coverage preempt ∨ AllowedipsCoverageNeeded coverage (preempt+512)) ∧
    KcovBufferBytes coverage a

def AllowedipsMetadata (coverage : KcovLayout) (preempt : BitVec 32) (a : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 a ∨
  ((LookupSoftRead preempt ∨ LookupSoftRead (preempt+512)) ∧ InRange (coverage.task+0x704) 4 a) ∨
  ((LookupModeRead coverage preempt ∨ LookupModeRead coverage (preempt+512)) ∧ InRange (coverage.task+0x6e0) 4 a) ∨
  ((AllowedipsCoverageNeeded coverage preempt ∨ AllowedipsCoverageNeeded coverage (preempt+512)) ∧
    (InRange (coverage.task+0x6e4) 4 a ∨ InRange (coverage.task+0x6e8) 8 a)) ∨
  (LookupPendingRead preempt ∧ InRange softirqPendingAddress 2 a)

def AllowedipsServiceBytes (coverage : KcovLayout) (preempt : BitVec 32) (a : BitVec 64) : Prop :=
  AllowedipsMetadata coverage preempt a ∨
  ((AllowedipsCoverageNeeded coverage preempt ∨ AllowedipsCoverageNeeded coverage (preempt+512)) ∧
    KcovStorageBytes coverage a)

/-- Outer saves/local words, the shared call slot, and the deepest peer-get
    saves/call: every word of this interval is used on a covered path. -/
def AllowedipsStackWrites (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec-144) 144

def AllowedipsLiveStack (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec-144) 152

def AllowedipsCountWrites (c : AllowedipsRelation.Config) (v : AllowedipsRelation.View)
    (a : BitVec 64) : Prop :=
  ∃ pid count, c.focus.peer = some pid ∧ v.count = some count ∧ count ≠ 0 ∧
    InRange (c.peers pid + .ofNat 64 Layouts.peer_refcount) 4 a

/-- Physical entry domain for both IP families. Focus is a total pure source
    selection, not an assumption that the binary or mirror terminates; a
    refused source search gives no selected node. No peer positivity premise.
    Both address families have executed concrete witnesses in AllowedipsWitnessPre. -/
structure AllowedipsEntry (c : AllowedipsRelation.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (returnAddress : UInt64) (s : MachineState)
    (world : Leanux.World) (v : AllowedipsRelation.View) : Prop where
  pc : s.pc = AllowedipsImage.Lookup.entry
  entry : EntryFrame s returnAddress
  root : s.data.regs.rdi.toBitVec = AllowedipsRelation.pointer c.nodes c.root
  bits : s.data.regs.get (.low .rsi .W8) = .ofNat 8 c.bits
  projection : AllowedipsRelation.project c world = some v
  related : AllowedipsRelation.R c [s] [LookupObservation.call "lookup" s] s world
  focusNode : c.focus.node = (AllowedipsSource.select v.nodes c.root c.bits c.key).join
  focusPeer : c.focus.peer = c.focus.node.bind (fun id => (v.nodes id).bind (·.peer))
  input : Allowedips.NetworkKey s.data.dmem s.data.regs.rdx.toBitVec c.bits c.key
  stack : ∀ i < 18,
    (s.data.dmem.loadInt (s.data.regs.rsp.toBitVec-.ofNat 64 ((i+1)*8)) 8).isSome = true
  preemptField : load32 s.data.dmem preemptCountAddress = some preempt
  coverageBefore : AllowedipsCoverageAt coverage preempt s.data.dmem
  coverageDuring : AllowedipsCoverageAt coverage (preempt+512) s.data.dmem
  hardirq : (preempt+512) &&& 0x000f0000 = 0
  pending : LookupPendingRead preempt → s.data.dmem.loadInt softirqPendingAddress 2 = some 0
  stackData : ∀ a, AllowedipsRelation.Reads c v a → ¬AllowedipsStackWrites s a
  stackInput : ∀ a, Allowedips.NetworkReads s.data.regs.rdx.toBitVec c.bits a → ¬AllowedipsStackWrites s a
  stackServices : ∀ a, (AllowedipsServiceBytes coverage preempt a ∨ InRange preemptCountAddress 4 a) →
    ¬AllowedipsStackWrites s a
  bufferData : ∀ a, AllowedipsRelation.Reads c v a → ¬AllowedipsCoverageWrites coverage preempt a
  bufferInput : ∀ a, Allowedips.NetworkReads s.data.regs.rdx.toBitVec c.bits a →
    ¬(AllowedipsCoverageNeeded coverage preempt ∧ KcovBufferBytes coverage a)
  bufferStack : ∀ a, AllowedipsCoverageWrites coverage preempt a → ¬AllowedipsLiveStack s a
  bufferMetadata : ∀ a, AllowedipsCoverageWrites coverage preempt a →
    ¬AllowedipsMetadata coverage preempt a
  bufferPreempt : ∀ a, AllowedipsCoverageWrites coverage preempt a → ¬InRange preemptCountAddress 4 a
  countStack : ∀ a, AllowedipsCountWrites c v a → ¬AllowedipsLiveStack s a
  countTrie : ∀ a, AllowedipsCountWrites c v a →
    ¬AllowedipsRelation.TrieReads c.nodes v.nodes c.root c.bits c.key a
  countServices : ∀ a, AllowedipsCountWrites c v a →
    ¬(AllowedipsServiceBytes coverage preempt a ∨ InRange preemptCountAddress 4 a)
  preemptData : ∀ a, AllowedipsRelation.Reads c v a → ¬InRange preemptCountAddress 4 a
  preemptStack : ∀ a, AllowedipsLiveStack s a → ¬InRange preemptCountAddress 4 a
  preemptServices : ∀ a, AllowedipsServiceBytes coverage preempt a → ¬InRange preemptCountAddress 4 a

/-- The function's named machine-entry domain, witnessed before it lands. -/
def Pre_allowedips (c : AllowedipsRelation.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (returnAddress : UInt64) (s : MachineState) (world : Leanux.World) : Prop :=
  ∃ v, AllowedipsEntry c coverage preempt returnAddress s world v

/-- Literal instruction agreement for the anchored insertion image. Callback
behavior and agreement with supplied random draws are separate obligations. -/
def IndexInsertDecoderAgreement (fetch : Int64 → Option Decoded) : Prop :=
  ∀ pc instruction, IndexInsertImage.Insert.fetch pc=some instruction → fetch pc=some instruction

/-- Read locations of instrumentation in the random call's unchanged BH
phase. Pending-work words and the insertion heap do not belong here. -/
def RandomMetadata (coverage : KcovLayout) (preempt : BitVec 32) (a : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 a ∨ InRange preemptCountAddress 4 a ∨
  (LookupSoftRead preempt ∧ InRange (coverage.task+0x704) 4 a) ∨
  (LookupModeRead coverage preempt ∧ InRange (coverage.task+0x6e0) 4 a) ∨
  (AllowedipsCoverageNeeded coverage preempt ∧
    (InRange (coverage.task+0x6e4) 4 a ∨ InRange (coverage.task+0x6e8) 8 a))

def RandomBuffer (coverage : KcovLayout) (preempt : BitVec 32) (a : BitVec 64) : Prop :=
  AllowedipsCoverageNeeded coverage preempt ∧ KcovStorageBytes coverage a

def RandomRecordingActive (coverage : KcovLayout) (preempt : BitVec 32) : Bool :=
  @decide (AllowedipsCoverageNeeded coverage preempt) (by
    unfold AllowedipsCoverageNeeded LookupModeRead
    infer_instance)

/-- A bounded physical stack reservation, not an instruction/draw budget.
The live range also protects the service return word. -/
def RandomStack (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec-1024) 1024
def RandomLiveStack (s : MachineState) : BitVec 64 → Prop :=
  InRange (s.data.regs.rsp.toBitVec-1024) 1032

/-- Current initialized provider state, recording graph and physical call
resources. This contains no World, source result or future execution premise.
The entry theorem must additionally separate these private writes from its
own represented objects and saved caller frame. -/
structure RandomReady (privateState : RandomProvider.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (s : MachineState) : Prop where
  coverageState : AllowedipsCoverageAt coverage preempt s.data.dmem
  preemptState : load32 s.data.dmem preemptCountAddress=some preempt
  capacity : AllowedipsCoverageNeeded coverage preempt → 0<coverage.capacity.toNat
  privateCheck : RandomProvider.check privateState coverage.task.toNat
    (RandomRecordingActive coverage preempt) s.data.dmem=.ok ()
  kernelMode : s.data.system.cpl=0
  forward : s.data.system.bits[10]=false
  stackMapped : ∀ i<1024, (s.data.dmem.get? (s.data.regs.rsp.toBitVec-1024+.ofNat 64 i)).isSome=true
  privateApart : ∀ a, RandomProvider.PrivateBytes privateState a →
    ¬(RandomLiveStack s a ∨ RandomMetadata coverage preempt a ∨ RandomBuffer coverage preempt a)
  stackApart : ∀ a, RandomLiveStack s a →
    ¬(RandomMetadata coverage preempt a ∨ RandomBuffer coverage preempt a)
  bufferApart : ∀ a, RandomBuffer coverage preempt a → ¬RandomMetadata coverage preempt a

def RandomWrites (privateState : RandomProvider.Config) (coverage : KcovLayout)
    (preempt : BitVec 32) (s : MachineState) (a : BitVec 64) : Prop :=
  RandomProvider.PrivateBytes privateState a ∨ RandomStack s a ∨
    (AllowedipsCoverageNeeded coverage preempt ∧ KcovBufferBytes coverage a)

/-- Unproved physical get_random_u32 service specification for the initialized
provider, including its recording hook. It executes the same fetched ISA as
the caller and preserves physical private readiness, coverage and BH state.
It promises no particular random value. Agreement with a recorded input tape
is a separate safety hypothesis; this declaration cannot produce arbitrary
requested draws from one fixed machine state. -/
def RandomReturnContract (fetch : Int64 → Option Decoded) (privateState : RandomProvider.Config) : Prop :=
  ∀ coverage preempt s returnAddress, s.pc=.ofNat 0xffffffff81375000 →
    RandomReady privateState coverage preempt s → EntryFrame s returnAddress →
    Eventually (historyStep fetch) (fun t =>
      Returned s t.machine returnAddress ∧
      EqualOutside (RandomWrites privateState coverage preempt s) s.data.dmem t.machine.data.dmem ∧
      AllowedipsCoverageAt coverage preempt t.machine.data.dmem ∧
      load32 t.machine.data.dmem preemptCountAddress=some preempt ∧
      RandomProvider.check privateState coverage.task.toNat
        (RandomRecordingActive coverage preempt) t.machine.data.dmem=.ok () ∧
      t.machine.data.system.bits[9]=s.data.system.bits[9] ∧
      (∀ point ∈ t.history.dropLast, IndexInsertImage.Insert.fetch point.pc=none))
      ⟨s,[s]⟩

/-- Safety coupling with an external recorded-input interpretation. The
interpretation depends only on provider-private bytes, never the WireGuard
heap. Recording context and return site are fixed parameters: changing either
can change a steered result without changing private bytes. The current
readiness and entry frame are premises of the return law, not conclusions.
Its return law constrains existing actual service histories; it does
not assert termination, physical readiness, a source insertion result or R.
In particular `inputAt` is required before a draw can be prescribed. -/
structure RandomInputCoupling (fetch : Int64 → Option Decoded) (privateState : RandomProvider.Config)
    (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (inputAt : DataMem → List Leanux.HiddenRecord → Prop) : Prop where
  frame : ∀ before after records,
    (∀ a, RandomProvider.PrivateBytes privateState a → before.get? a=after.get? a) →
    inputAt before records → inputAt after records
  returned : ∀ s t history records value rest,
    s.pc=.ofNat 0xffffffff81375000 → RandomReady privateState coverage preempt s →
    EntryFrame s returnAddress → inputAt s.data.dmem records →
    Pair.Insert.draw records=.ok (value,rest) →
    ActualHistory fetch s history → history.getLast?=some t →
    Returned s t returnAddress →
    (∀ point ∈ history.dropLast, IndexInsertImage.Insert.fetch point.pc=none) →
    (t.data.regs.get (.low .rax .W32)).toNat=value ∧ inputAt t.data.dmem rest

end Binary.TrustBase
```
