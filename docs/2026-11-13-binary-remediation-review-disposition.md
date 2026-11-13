# Binary remediation plan: review disposition

Disposition and proposed remedies [AGENT 2026-11-13]. Two independent
reviewers examined draft `2c020e31`, in separate worktrees without the
conversation or each other's conclusions. Their briefs supplied the
revision, setup and objectives, with no restriction on review questions
or required verdict. The records are [review A](2026-11-13-review-binary-remediation-a.md)
and [review B](2026-11-13-review-binary-remediation-b.md).

All five findings are accepted. The changes below repair the
[plan](2026-11-13-binary-remediation-plan.md); they do not claim to repair
the implementation. Both reviewers have rechecked revised plan `a616d1fe`
and found their findings addressed at the plan level. This record preserves
the original findings and their individual
disposition rather than replacing them with a combined verdict.

| Finding | Disposition in the plan | What implementation must demonstrate |
| --- | --- | --- |
| A-F1, high: caller establishment is missing from the composition obligation | Fixed in stages 5 and 6. Every edge must derive the next entry from the prior result/invariant and the actual permitted caller transition; progress to the call is an additional obligation when claimed. Edges are classified as instruction-proved or assumed under a named external contract. In-scope WireGuard callers cannot silently become environment assumptions. | The resulting theorem must discharge those edges or state its caller assumptions. A `Covered` theorem that assumes every next `Starts` is insufficient for a caller-verification claim. |
| A-F2, medium: completed-syscall prefix is not the function-entry source cut | Fixed in stage 1 and the first batch. Replay must advance through the current syscall to the same cut and preserve the remaining hidden-input stream. A pre-syscall difference is not automatically a mirror defect. Local state-input claims stay separate if alignment cannot be observed. | A source state independently computed at the matching cut, without fitting it to the captured heap or rewriting the mirror for proof convenience. |
| A-F3, medium: admission and completed proof have ambiguous exits | Fixed in the common status definitions and stages 3–6. Admission-ready permits proof work; proved-and-accepted requires the theorem and applicable local/external acceptance for the exact closure. Pending external acceptance and unresolved scope remain explicit. | Reports must name the actual status and scope, and never promote passing captures into a completed proof stage. |
| B1, medium: totals can hide sampling gaps and omitted invocations | Fixed in stage 2 and the stage-5/6 exits. The selected interval needs continuous observation and exact collector totals independent of retained predicate events. Site coverage metadata survives conversion and is checked before predicates. An omission/quota control must fail completeness. | No missing relevant call, lifetime event or boundary in the validated interval. An inexact or sampled interval remains diagnostic, even if its retained predicates all pass. |
| B2, medium: old trust roots omit recovered claims | Fixed in the build/acceptance discipline. Each unit extends the existing terminal/import/predicate lists and the export/replay closure, including bridges and source checks for proof subdirectories. | Axiom and kernel acceptance evidence must include the actual new headline and bridge at the reported revision, rather than only the historical October roots. |

Review A's remaining frame-feasibility concern is also made explicit in
stage 3: the first C2 experiment must produce a concrete observation domain
and executable frame method or return unresolved. The archived sparse
window/nonce/count capture does not establish the native `EqualOutside`
frame. No stronger admission or proof result is claimed by this plan edit.

The inspection also leaves genuine implementation questions: obtaining
the matching source cut without changing mirror behavior, observing the
required native frame under ordinary scheduling, realizing the required
workload cases on the selected clean image, and resolving non-executable
universal assumptions. These have stop conditions rather than presumed
solutions or invented completion dates.

## Follow-up outcome

Both review documents include their follow-up on `a616d1fe`, with exact
references. Review A reports no remaining material objection to the bounded
first investigation batch; review B reports no remaining or newly introduced
material finding in the revised proposal. Neither claims the implementation
obligations are solved. The plan's substantive text is unchanged after that
reviewed revision; later commits collect the reviews and this disposition.

The proposed next action is the three-item first batch at the end of the
plan, with admission and feasibility findings as its output. Implementation
has not begun as part of this planning/review task.

## Evidence and limits of this review cycle

Review A used source inspection. Review B additionally ran a bounded
Python check showing that archived event conversion drops final inexact
site-coverage metadata. That experiment does not demonstrate an end-to-end
false acceptance by the Lean evaluator. Neither review reran the earlier
assessment's captures or established new binary correctness results.

The change set is documentation only. Validation of the plan checks local
links, whitespace and consistency with the inspected command/statement
definitions. Full Lean builds, guest runs and external kernel acceptance
belong to implementation claim points and have not been repeated for this
document. No standing rule, model, oracle, theorem or main branch is changed.
