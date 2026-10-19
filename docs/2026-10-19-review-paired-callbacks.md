# Independent review of the shared-callback increment

Status: interim review while implementation continues. This is not a closing
verdict. The inspected committed checkpoint is `ae3f1e68`, including the
first-return mutator proofs from `5d295d83`; conditional-read test changes were
also visible during review. The charter and current report were read whole.

The five callback image proofs and their applications are substantial progress
on the stated trust-reduction goal. I found no soundness defect in the inspected
contracts, decoder transport, guarded execution machinery, or removal and
replacement first-return headlines. Lookup first-return and its use in the
non-inserting sequence remain unfinished, so the increment does not yet meet
its success criterion. Final validation, reporting and external acceptance are
also outstanding.

## Findings to disposition

### R1 — Conditional resource reads were not exercised by the initial suite

Severity: medium, validation gap. The initial `CallbackRun.fixture` mapped all
task metadata and the softirq-pending word. Varying their values exercised
branch effects, but could not reveal an unnecessarily strict readiness clause
or an unintended read on an early-return path. The charter specifically calls
for these read dependencies to be tested.

The author has added `conditionalReads`, which physically removes unread
fields for positive cases and required fields for negative cases. It includes
the BH nested-count path with an absent pending word. That is the appropriate
repair. On reinspection, the independently reproduced executable run passed
all 17 conditional positives and 39 negatives, in addition to 3,032 KCOV and
50 BH cases. R1 is fixed. The universal proofs were not weakened to accommodate
this finding.

### R2 — Negative controls initially accepted unrelated execution failures

Severity: medium, test honesty. The first version of the new `checkRejected`
accepted every `execute` error. This includes `callback.instruction-budget`
and unrelated decoding or interpreter failures. Such a failure does not
establish the intended missing-resource behavior and must not make the control
green.

Require the expected error class/site, or at least reject budget exhaustion
and unrelated fetch failures. The pending-work and hardirq controls have
different expected boundaries from missing-memory controls and should be
identified explicitly. This affects evidence from the test, not the proved
image contracts.

Disposition: fixed. `checkRejected` now requires an exact expected error.
Missing-memory cases identify the address and read/write kind; pending work
must reach the excluded service entry, and hardirq must reach the rejected
UD2 site. Budget exhaustion or another error makes the suite fail. The
independent run passed. Four missing-return-word controls reject in the
runner's initial `readNat`, before instruction fetch; they establish entry
rejection, not an ISA-executed memory fault. The report should preserve that
distinction.

### R3 — The non-inserting sequence still uses the broader permission premise

Severity: medium, incomplete deliverable. At the inspected checkpoint,
`Binary.Pair.Sequence.sequence_from_image` still takes
`ReturningDomainPermissions`. The bounded charter retains this broader form
for insertion and mixed sequences containing insertion; lookup, remove and
replace are the first-return targets. After lookup's first-return theorem
lands, the non-inserting sequence should use `FirstReturnDomainPermissions`
and retain the per-call first-return fact for the same histories that establish
its postconditions. If it does not, the report must identify that outstanding
boundary explicitly rather than reporting full completion.

This is not a claim that the existing broader theorem is false. The report
already labels sequence integration as unfinished.

## Trust-surface inspection

`ServiceDecoderAgreement` is instruction/length agreement with the literal
partial decoder. It does not repackage a behavioral callback assumption.
`bh_contract`, `pc_contract` and the three comparison contracts apply proved
image theorems through this agreement. The comparison wrappers use one shared
comparison body. The existing `KcovReady` and `BhEnableReady` predicates are
unchanged from the baseline.

The service proofs use actual fetched instructions and preserve universal
undefined outcomes. `leafGuard` constrains the stack throughout service
interiors and excludes anchored reentry; its endpoint is allowed to be the
actual return. Rejection of the unreachable UD2 is a missing fetch, not a
successful no-op. The external ELF/parser/hardware interpretation remains
outside the Lean result, as stated in `TrustBase.lean`.

`BeforeOuterReturn` uses the return PC together with the consumed outer stack
word, rather than the address of a syntactic RET instruction. Its proper-prefix
condition excludes the unexecuted continuation. `FirstReturnCallPermissions`
quantifies actual finite prefixes and asserts access safety, not termination
or reconstruction. The removal and replacement headlines construct their
actual histories from guarded execution and export the postcondition,
first-return property and permission audit for the same history. Removal's
tail call to BH-enable is covered. No exclusion of return-PC/code aliases or
additional entry-domain restriction was introduced for this argument.

`StackPath` and `StackCps` are semantic proof obligations. The tactic chooses
a proposed stack delta and produces a proof against instruction semantics;
its choice is not an axiom or a certificate-checker assumption. The current
mutator compositions duplicate portions of the old composition scripts. That
is a maintenance and measurement cost, accurately acknowledged in the report.

## Lookup integration assessment

The old endpoint theorem cannot establish the new interior property by itself.
`LookupPost.noEarly` derives absence of an earlier visit to the syntactic outer
RET from observed return counts. It does not independently exclude an earlier
state at the outer ABI-pair boundary.

A promising reusable route is to lift the existing fixed-history region
theorems: their postconditions describe the actual appended state lists, so
stack exclusion can be proved over those lists without repeating instruction
calculations. A generic extraction lemma can turn a history execution whose
proper-prefix states satisfy a guard into guarded execution. The nonemptiness
needed to justify the current guard is available from
`NondetSupportingType.from_hash`; universal undefined outcomes must remain
universal in the transformed proof. Bucket and helper composition must still
carry the strengthened history invariant. This is a suggested construction,
not a completed proof or an assumption that the missing composition is cheap.

Follow-up inspection: `HistoryGuard.lean` now implements this generic
construction. Its witness selection establishes the current-state guard;
`instruction_mono` then retains all successor branches in the transformed
execution. `history_guard_suffix` uses the actual appended state list. I found
no soundness defect in these lemmas, and independent axiom prints for
`history_guard`, `history_guard_suffix` and `guarded_history_project` report
only the three standard axioms. Their application to lookup remains unfinished.

A separate control-flow/stack invariant over actual histories is another
sound route, but indirect returns and preservation of saved return slots make
it a real proof obligation. I did not find a ready-made global invariant in
the existing lookup postcondition that eliminates this work.

## Independent checks and remaining close

Both commands exited zero, independently of the author's build:

```sh
capped lake env leanchecker --fresh PairRemoveFirstEnvironment
capped lake env leanchecker --fresh PairReplaceFirstEnvironment
```

An earlier invocation supplied both modules to one `--fresh` command and failed
because that CLI accepts a single module. The separate runs above are the
corrected checks; the failed invocation is not counted as a pass.

An independent `#print axioms` invocation reported only `propext`,
`Classical.choice` and `Quot.sound` for all five ambient callback contracts,
both mutator first-return headlines, `lookup_from_image`, and both finite
sequence image corollaries. These are local checks, not external export
acceptance.

Closing review must revisit R1–R3, the finished lookup/sequence statements,
scoped positive workloads and witnesses, final pins and clean dependency,
the complete report including TrustBase verbatim, and the exact-commit export.
The scientific conclusion should distinguish cheap callback-wrapper/client
reuse from the additional first-return composition cost; this increment alone
does not measure the cost of the remaining whole campaign.

The follow-up test command was `capped .lake/build/bin/binary-callbacks` from
`binary/`. It exited zero with 51,935 instructions across the successful
generated cases, 17 conditional positives, 39 negatives, 3,032 KCOV cases and
50 BH cases. The supplied build log records a successful rebuild of the
changed executable. R1 and R2 are closed; R3 and the final increment verdict
remain open.
