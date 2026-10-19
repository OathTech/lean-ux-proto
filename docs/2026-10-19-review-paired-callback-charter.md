# Independent review: shared callback charter

Reviewed 2026-10-19 at `9388321498a86393ea4f0e76113d2c1907c9c064`, on
`task/binary-pair-runner`. This is a review of the proposed increment and its
supporting definitions, not acceptance of new proofs or of the pending insertion
export. No implementation, build, dependency or other-worktree changes were made.

**Verdict: revise the first-return deliverable before treating the complete
charter as executable.** The five callback proofs are a useful, coherent next
increment. The requirement to combine first-return permissions with insertion
and insertion-containing sequences has an additional dependency that the charter
does not budget or permit explicitly. There is one high-severity finding below.

## R1 — High: insertion first-return safety needs a random-service interior proof

The [charter](2026-10-19-charter-paired-callbacks.md), lines 28–32, 50–54,
71–74 and 83–85, requires permission safety through the first outer ABI return,
for the same execution that establishes the postcondition, while retaining
`RandomReturnContract` and `RandomInputCoupling` as the outstanding random-service
assumptions. Those assumptions do not establish the needed execution boundary.

Checkable dependencies:

- [TrustBase.lean](../binary/TrustBase.lean), lines 681–693:
  `RandomReturnContract` constrains the eventual ABI return, endpoint memory
  frame, endpoint provider/coverage/preempt state and interrupt flag. Its only
  interior-history condition excludes PCs decoded by `IndexInsertImage.Insert`.
  It does not constrain intermediate stack depth, preserved registers, transient
  memory writes, or visits to the outer caller's return boundary.
- The same file, lines 703–716: `RandomInputCoupling.returned` constrains the
  result and input cursor of an actual service return. It adds no interior
  control-flow restriction. An intermediate outer return outside insertion's
  instruction range is not excluded by either condition.
- [RandomService.lean](../binary/RandomService.lean), lines 28–48, and
  [PairInsertRandomCall.lean](../binary/PairInsertRandomCall.lean), lines 13–57:
  the random call is composed using those endpoint facts. Its local history
  is projected away; no first-outer-return fact is derived.
- [PairInsertEnvironment.lean](../binary/PairInsertEnvironment.lean), lines
  10–31, and [PairInsertSequenceExecution.lean](../binary/PairInsertSequenceExecution.lean),
  lines 49–80: the permission conclusion currently follows from the deliberately
  broader `ReturningCallPermissions`. Replacing its premise with permission
  safety only up to the first return requires a new theorem about these histories.

The missing implication can be checked without assuming a kernel bug. Consider
an ambient decoder that agrees with the insertion and five service images but
implements the still-abstract random service with a detour. It saves its state
in its mapped private stack, temporarily restores the outer ABI register/stack
state and reaches an outer return address outside the insertion image. Code at
that address restores the service state; the service subsequently completes its
ordinary return and the insertion finishes. Its endpoint frame and input result
can be unchanged, and its proper history need never execute an insertion PC.
The current contracts impose no condition ruling out this detour. The outer
heap need not satisfy the insertion postcondition at the earlier boundary.
This is a counterexample pattern to the proposed logical implication, not an
executed counterexample to the pinned Linux image; no such kernel behavior is
claimed here.

The required additional fact is **safety of the actual random-service interior**:
for the service invocation reached from insertion, prove that every proper
prefix up to its service return avoids the outer invocation's ABI-return
boundary. A stack-depth and return-slot invariant is one possible proof route.
This is weaker than proving the complete random output/effect/termination
contract, but it must follow from the fetched instructions and established
physical state. Endpoint framing alone is insufficient. The result must then be
carried through the caller's execution composition; merely strengthening a
definition of the permission premise does not discharge it.

The proof is not obviously a small consequence of the five callbacks.
[RandomImage.lean](../binary/RandomImage.lean) contains 1,267 instruction rows
across the provider and recording closure, including nontrivial nested calls and
memory-writing paths. The current source includes the formerly missing
PUSHF/CLI/STI semantics; the early missing-instruction note in the insertion
report was superseded. Therefore that old note is not a current blocker.
Nevertheless, no corresponding random-service interior invariant was found.
A general proof would need to account for the relevant dynamic return words
and supported branches, not just the sampled cached-service path.

**Requested disposition:** settle this dependency before implementing the
insertion first-return headline. Either make the extra instruction-derived
safety proof an explicit, separately calibrated deliverable, or separate the
five-callback increment from the insertion first-return work. In the latter
case, all existing insertion/mixed-sequence headlines can still be instantiated
with the five proved contracts while retaining their documented broader
permission hypothesis; first-return claims can be limited to calls/sequences
whose only services are the five proved callbacks. Do not obtain the missing
result by adding an unproved random-service boundary assumption or a successful
execution premise. A scope decision must be reflected in the charter's success
criterion, not reported later as full completion of the original criterion.

## Assessment of the remaining plan

The callback objective is substantive. The five hypotheses are explicit in
[PairInsertSequenceAdequacy.lean](../binary/PairInsertSequenceAdequacy.lean),
lines 92–115; the common callers already derive readiness and retain resources.
[PairServiceCall.lean](../binary/PairServiceCall.lean), lines 10–33 and 35–94,
is a genuine reuse point. Proving image contracts and supplying them here removes
behavioral assumptions from consumers without changing reconstruction or the
mirror. Retaining the original general conditional lemmas is appropriate.

The literal service listing supports the proposed division: BH-enable, PC
recording, one comparison body and three wrappers. I compared its branch/read
order and store calculations against `KcovPlan`, `KcovReady`, `KcovEffect` and
`BhEnableReady` in `TrustBase.lean`, lines 254–338. I found no additional concrete
contract counterexample in this inspection. That is not proof of those contracts.
Testing the actual fetched bodies against these same definitions, especially
wrapped counts, aliased planned destinations, conditional metadata reads and
the return-word exclusion, is a sound discovery step. The image proofs must
still quantify over the unspecified instruction outcomes.

The first-return boundary should be stated as an ABI boundary of the outer
invocation and exported on its actual history. The charter correctly rejects
both a fixed RET-site shortcut and a final-PC-only shortcut. Nonrandom callers
also require an interior proof: their present endpoint lemmas do not gain this
property automatically when the service hypotheses are discharged. Designing
that compositional fact alongside the callback proofs will avoid throwing away
the needed history information.

For cost viability, this is a reasonable bounded calibration, not yet a measured
campaign rate. Separate discovery, proof, consumer integration, review and
validation costs as proposed. Report the first service/body cost and each later
wrapper/consumer separately; keep first-return infrastructure and any random
safety work separately identifiable so they do not obscure the callback reuse
measurement. The first-callback reassessment and honest partial-checkpoint stop
rule are necessary; an eight-hour bound is an experiment, not evidence that
every deliverable already fits.

Inspection confirmed the private Kraken checkout is clean at
`cd2ae360bfcf8e1fc719793405811ff49c3e75ce` and the binary toolchain file names
Lean 4.35.0. I did not rehash the oracle, rerun the earlier acceptance checks,
or execute new tests. The insertion export remains externally pending, and
this review does not change the existing mirror-lag status. Only this report
was written.
