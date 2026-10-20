# Independent review of the shared-callback increment

Status: local closure supported at `86ea5488`, after the initial review
at `ae3f1e68` and the conditional-read repairs. R1–R3 are fixed. No remaining
proof-surface blocker was found. The report, README and register have been
checked; final captured replay, full-closure replay and exact-commit export
all completed successfully. External acceptance is pending. The charter and
current report were read whole.

The five callback image proofs and their applications are substantial progress
on the stated trust-reduction goal. I found no soundness defect in the inspected
contracts, decoder transport, guarded execution machinery, or the completed
lookup/removal/replacement first-return headlines. The non-inserting sequence
now retains the first-return property for each actual call history. This closes
the mathematical deliverable identified in the initial review. Local validation
is complete; the prepared export still requires the external acceptance gate.

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

Disposition: fixed at `86ea5488`. The new
`Binary.Pair.Sequence.First.sequence_checked` takes
`FirstReturnDomainPermissions`. A first closing version applied permissions
to the correct history but discarded the boundary fact when packaging the
old `Observed` predicate. Review caught this additional export gap. The new
`First.SequencePost` conjoins the existing sequence postcondition with
`BeforeOuterReturn` for every retained call record's own entry and history.
The induction retains that fact for each call. Independent inspection of the
rebuilt declaration confirms this exact statement, and its axiom print is
standard. The old broader theorem remains available; no claim was made that
it was false.

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
only the three standard axioms. Their application to lookup was unfinished at
that checkpoint and is covered by the closing inspection below.

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

Closing review revisits R1–R3 and the finished lookup/sequence statements
below. Combined scoped workloads, final pins and clean dependency, the
complete report including TrustBase verbatim, and the exact-commit export
were still being prepared at the latest inspection.
The scientific conclusion should distinguish cheap callback-wrapper/client
reuse from the additional first-return composition cost; this increment alone
does not measure the cost of the remaining whole campaign.

The follow-up test command was `capped .lake/build/bin/binary-callbacks` from
`binary/`. It exited zero with 51,935 instructions across the successful
generated cases, 17 conditional positives, 39 negatives, 3,032 KCOV cases and
50 BH cases. The supplied build log records a successful rebuild of the
changed executable. R1 and R2 closed at this checkpoint; R3 closed during the
subsequent inspection recorded above.

## Guarded lookup construction: subsequent inspection

The next inspection covered the new `guarded_forget`, `guarded_lift`,
`guarded_prefix`, `guarded_last`, `GuardedSegment.bind`, guarded call/scan
composition and peer stack-slot inference. No soundness defect was found.

`guarded_lift` permits an arbitrary starting history, but claims neither its
actuality nor that it ends at the starting machine state. The separate
`guarded_last` premise and eventual actual-history construction remain
necessary. The inspected uses preserve that distinction. Forgetting a history
does not establish observations for a different history: it only projects the
stated endpoint predicate.

`GuardedSegment.bind` composes two executions under the same guarded
instruction semantics. Its audit-composition argument is a proved property of
the instantiated audit, not a behavioral execution premise. The scan uses
`StableTrace.trans` to supply it. It does not replace either segment with an
unexecuted annotation.

`StackSlots` is a proof-local exclusion for the helper's eight possible stack
positions. `lookup_slots` derives it for a helper entry at `outer - 48`;
the deepest service slot is `outer - 104`. The arithmetic is modular and no
new stack-range assumption is required. `slots_guard` selects one of eight
candidate positions, then proves the equality; an incorrect selection does
not bypass the kernel.

Independent axiom prints succeeded for the four guarded helpers, segment
composition, `lookup_slots`, lookup's entry/header/bucket theorems, and peer
start/finish/null-entry. Only the standard axioms occur (`lookup_slots` uses
only `propext`). This is an axiom check on the currently built modules, not a
closing replay or a claim that the full function is complete.

There remains avoidable proof duplication, particularly the unchanged
observation/frame post-processing in `LookupFirstEntrySimulation`,
`FirstScanIteration` and the higher compositions. A specific future factoring
is to extract those blocks as pure implications from a raw region postcondition
to its richer postcondition. Both the old and guarded executions could apply
the same implication with `eventually_weaken`. That would preserve the tested
execution and correspondence structures while removing duplicated bookkeeping.
This is a reuse opportunity, not a correctness finding or a reason to expand
the current bounded increment. The present report should count the copied
composition as maintenance cost and distinguish it from reused instruction
proofs.

## Completed lookup and sequence: closing mathematical inspection

The inspected source checkpoint is `86ea5488`. `lookup_first_return` obtains
the guarded execution from the unchanged executable `Pre` and accepted mirror
run. The outer theorem starts with `[initial]`, constructs `ActualHistory`,
retains the last-state equation, and derives `BeforeOuterReturn` from the
proved stack guard. Its permission audit applies to that same history. The
sequence theorem constructs the same facts independently for each explicitly
prepared call, then retains every boundary in `First.SequencePost`.

The physical bucket loop and NULL/dead/live peer-get branches remain present.
The helper stack-slot exclusions follow from modular arithmetic, including
wraparound, rather than extra assumptions in `Pre`. Dead-peer null storage
through the owner is retained. Return-address/code aliases remain admitted.
The use of a witness to recover a current-state guard does not restrict
undefined outcomes: transformed instruction steps still prove every branch.
`guarded_mapped` preserves the mapping resources on the actual guarded
execution using the existing store-stability theorem. It supplies no future
precondition or successful execution as an assumption.

The diff from `d61a8027` adds exactly four declarations to `TrustBase.lean`:
`ServiceDecoderAgreement`, `BeforeOuterReturn`,
`FirstReturnCallPermissions` and `FirstReturnDomainPermissions`. Existing
readiness predicates and reconstruction clauses are unchanged. Insertion
and mixed insertion explicitly retain `ReturningCallPermissions` or
`ReturningDomainPermissions` and the random-service contracts, as permitted
by the bounded charter. The new service agreement specifies instruction
decoding, not service behavior.

Independent imports of the rebuilt `PairCallbackSurface` and prints of
`First.SequencePost`, `First.sequence_checked` and `lookup_first_return`
confirmed the repaired statements and only standard axioms. The printed
trust-surface diff preserves the old statements and adds the new public
statements and sequence-post definition. This verifies the local compiled
surface; it is distinct from the full-closure replay subsequently completed
below and from external acceptance.

The evidence supports the bounded trust-reduction result. Five behavioral
service premises have been discharged from literal instructions, and the
non-inserting clients now expose first-return histories under explicit
permissions. It does not establish concurrent contextual refinement, prove
real kernel-entry reachability, discharge insertion's random-service contract,
or establish campaign-wide proof economics. The considerable copied lookup
composition remains a real cost despite reuse of the instruction proofs.

## Documentation and closing checks

The final documentation pass checked the report, README and register at the
same code checkpoint. The report's TrustBase block matches the source file
byte-for-byte. An independent recount confirms 90 added Lean modules and
10,170 gross new lines. The report separates wall-clock intervals from
uninstrumented aggregate compute and separates reusable service work from
the much larger copied first-return composition. The limits and reproduction
commands make the remaining random-service contracts, explicit caller setup,
generated/reconstructed inputs and missing concurrent-context claim visible.

The trust-gate log ends in both trust-surface-diff PASS and binary proof-gate
PASS. All six gate unit tests passed. The author reported tracked exit status
zero for the final `leanchecker --fresh PairCallbackSurface`, rerun after the
explicit insertion environment corollary was added. The exact-commit
`leanexport PairCallbackSurface` also exited zero, producing 1,331,952,229 bytes
from `86ea5488e288998ea4aa0b26335c64428ffeaf04`. These completion statuses,
rather than an empty replay log or an export file alone, establish the local
check results.

The captured-insertion result was independently inspected: both seeds pass,
each comparing 33,626,368 bytes, with 1,338 interpreted instructions, 1,354
native single-step stops, two random services and the unchanged 4,194,304-word
coverage capacity. It identifies actual captured entry memory and includes
the failing system-flags corruption control. The author recorded successful
process completion. This runtime evidence does not prove the retained random
service contracts.

The independent finding dispositions and local closing checks are complete.
This review supports closing the bounded increment locally. External
acceptance still requires the user's export-based gate result for the named
code commit; prior gate results do not cover these new proofs.
