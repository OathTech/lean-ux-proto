# Paired index insertion: execution report

Status: started on `task/binary-pair-runner` at baseline `41675f86` under the
[charter](2026-10-18-charter-paired-index-insertion.md).

Start: **2026-10-18 17:23:07 UTC**. Reassessment if incomplete:
**2026-10-19 17:23:07 UTC**. Supporting runtime optimization allowance: two
focused hours, zero used. No merge, push or changes to mirror/oracle/global state.

Mirror pin `cb2348e` now lags main `783510e850e187549cbb9380e53790e1ed232c77`.
Private Kraken remains clean at `7ebba06a30eaf08c10b26b28ca14bfee1c791576`,
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

The start checkpoint had no new theorem or passing insertion test. Current
progress is recorded below; whole-function insertion adequacy remains open.

## Independent review disposition

The [surface review](2026-10-18-review-paired-index-subsystem.md) permits the
insertion extension on the existing conditional sequential foundation. It
found no circular future-Pre/execution premise. Each finding is retained:

- **R1, medium:** the old sequence permission domain covers arbitrary prepared
  heaps. The insertion extension will restrict the *permission quantifier* to
  a readiness domain derived by composition. This weakens the environment
  hypothesis, not the source domain or R. The prior exported theorem is unchanged.
- **R2, medium:** the old returning-history premise also covers histories that
  returned earlier and later reached the same boundary again. This is a stronger
  assumption, not a first-return safety result. It remains explicitly open while
  the insertion execution/history boundary is designed. Do not describe the
  current premise as excluding all executed caller continuations. A repair must
  derive a first-boundary property rather than assume future R or termination.
- Intermediate Ready is established and used by old composition, but absent
  from its exported per-call Observed relation. The extended theorem should
  expose the paired boundary states if its claimed observations require them.

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
