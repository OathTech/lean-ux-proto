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
