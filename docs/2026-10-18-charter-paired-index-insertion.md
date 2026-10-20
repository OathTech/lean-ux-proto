# Charter: paired index insertion and input-driven composition

[USER 2026-10-18] Extend the completed sequential index subsystem with insertion,
recorded random draws and collision retries. The objective is general refinement
of the compiled image under Kraken against the actual executable Lean mirror.
Execution tests discover bad abstraction and invariant candidates early; the
proved definitions must be the tested definitions. Tests are not the result.

Worktree `.worktrees/binary-pair-runner`, branch `task/binary-pair-runner`;
baseline `41675f86`. Start **2026-10-18 17:23:07 UTC**; reassess at
**2026-10-19 17:23:07 UTC** if incomplete. No merge or push. The fixed allocation
universe and sequential/no-pending-work environment remain explicit. Do not
change the mirror, approved oracle, global state or another worktree.

## Target and limits

Prove complete `wg_index_hashtable_insert` against `WG.indexInsert`, then
extend the arbitrary finite retained-heap sequence theorem to insertion,
lookup, handshake-to-keypair replacement and removal. The common executable
reconstruction compares bucket membership/order, owners and their peer words,
peer counts and linkage validity. Add only clauses justified by anchored
reads/writes or the stated observations. Callback and ABI resources are
separate physical readiness/frame conditions. External draw streams and their
consumption state are supplied environment, not reconstructed physical World.

The insertion theorem covers initially linked and unlinked owners, empty and
nonempty buckets, reinsertion, and any finite collision-retry prefix whose
actual mirror execution accepts. Derive that the locked second walk cannot
find a new collision under the sequential environment. Do not remove a real
path by merely assuming the desired walk outcome. Draw exhaustion remains an
explicit source refusal outside accepted-return adequacy; do not fabricate
fresh values or silently truncate retries.

The observation is interface results and reconstruction at call boundaries.
Internal correspondence points are proof choices. The sequence retains one
heap and allocation interpretation with explicit caller setup; derive every
later entry precondition from previous postconditions and source-only caller
obligations. No rematerialization, future-Pre assumption or successful future
binary-run premise. Allocation, freeing, RCU transitions, compiled callers
and concurrent contextual refinement are not added by this increment.

## Recorded-input boundary

The pinned insertion calls `get_random_u32`; its wrapper calls the raw entropy
provider and the recording hook. Any unproved random service behavior must be
named in `binary/TrustBase.lean`, exposed as a headline hypothesis, and distinguish
physical service readiness/frame from correspondence with the supplied draws.
Do not assert that the same fixed deterministic machine state returns every
possible supplied draw. Do not hide an insertion result, future reconstruction,
or successful insertion execution in an input/environment hypothesis. State
exactly which service instructions execute in each test and which boundary is
assumed; a supplied service return is not actual Kraken execution of its body.

## Work sequence and completion

1. Review the existing theorem/domain/trust surface independently. Record the
   preceding export gate when the user supplies its result; it remains pending
   until then. Proceed with independent preparation while it is pending.
2. Build insertion's paired executable and assertions from the image. First
   run the independent mirror-result/kernel-coverage/mirror-decision comparison.
   Exercise real captures and labelled generated retries, including negative
   controls for malformed or misplaced input records and new assertion classes.
3. Prove insertion's combined pointer effects and full function, including
   entry/return and all source-accepted retries. Formal positive Pre witnesses
   execute to return. Reuse existing unlink/chain/frame mechanisms where they fit.
4. Extend finite composition with exact ordered draw consumption. Execute mixed
   insert/lookup/replace/remove/reinsert sequences over retained memory. Prove
   the general theorem, not just a fixed sequence or bounded test case.
5. Build, print all headline/witness axioms, run fresh kernel replay, update the
   existing reviewable trust specification, and prepare an exact-commit export
   for the external `lake check --from-export` gate. One increment register row
   and one report record the theorem, assumptions, findings, provenance and cost.

Use direct region and endpoint proofs; no certificate checker. No sorry,
native reduction axiom, unsafe proof path or kernel-check bypass. Every new
assumption is named and reviewed, with concrete entry evidence. A mismatch is
investigated under Rule Zero; no narrowing of observations or valid dead-peer
states to conceal it. Public/global/oracle changes need separate authorization.

[AGENT 2026-10-18] Retain the bounded two-hour supporting runtime experiment:
measure any KCOV replay improvement with actual capacity unchanged and equivalent
comparisons. Stop that experiment at diminishing returns; insertion refinement
and composition are the deliverable. Do not claim smaller generated capacities
or fewer comparisons as unchanged-capture acceleration.

## Measurement and checkpoint

Record UTC stage boundaries and failures, including killed builds and timeouts.
Separate assertion discovery, diagnosis, fresh instruction proofs, reconstruction,
input coupling, composition and capture/validation. Record reused versus fresh
mechanisms and proof size; elapsed time is not aggregate compute or person-hours.
The main question is the marginal cost of a larger input-driven function after
the earlier two mutators. A completed runner alone is not completion. Work to
this checkpoint or report a concrete blocker/day-budget reassessment honestly.
All heavy commands use `capped`; applicable guests use `LEANUX_QEMU_SLOTS=16`.
