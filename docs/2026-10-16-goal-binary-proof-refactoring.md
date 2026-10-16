# Goal: example-driven binary-proof refactoring

[USER 2026-10-16] Create a separate branch/worktree from the paused binary
checkpoint, record this framing, and begin the find–factor–replace–measure
loop. Build reusable mechanisms by shrinking existing M1 and completed M2
proofs; retain their highest-level proof structures. Exercise judgment about
lemmas versus tactics and stop when further work has diminishing returns.
This experiment should be substantially shorter than the initial proof build.

## Fixed target and scope

Worktree: `.worktrees/binary-proof-refactor`. Branch:
`task/binary-proof-refactor`. Baseline: `6812d04`. The original
`.worktrees/binary-tv` remains paused and unchanged. Its incomplete M2 theorem
is not an objective of this experiment.

The existing proofs supply concrete examples and the regression suite. Keep
headline statements, Pre, R, trust declarations and highest-level proof
structure fixed. Keep the executable mirror, oracle, Kraken semantics and
pinned dependency commit fixed. This is proof refactoring, not a campaign
expansion, state-split migration or new composition architecture. No merge to
main, no push, no global configuration or shared-cache changes.

The charter's direct-proof method remains: no certificate checker, no new
axioms, no native reflection axiom, no sorry or unsafe proof escape. Generated
proofs or tactic applications must be accepted by the ordinary Lean kernel.
The three preserved `.lean.draft` files remain outside the build and outside
all acceptance claims.

## The working loop

1. Find a repeatedly written proof pattern in the current tree, with concrete
   examples and reason to expect further occurrences.
2. Factor its mathematical content into a small proved lemma.
3. Add a tactic only when application needs useful search or iteration beyond
   a short ordinary proof. Prefer predictable normalization and bounded,
   understandable procedures. Unsupported cases fail visibly.
4. Replace multiple real instances, including one outside the motivating
   family, without changing the statements being proved.
5. Measure what disappeared, the cost of the reusable mechanism, exceptions,
   and elaboration/kernel-checking effects. Retain only justified mechanisms.

Every mechanism earns its place by replacing existing proofs. Do not build a
speculative library first or turn an abstraction into a second project.
Lemmas express useful properties repeatedly proved. Tactics implement search
or iteration; they can exploit regular shapes but can also become a burden
when unpredictable. The choice is made per pattern, not by a tactic quota.

## Initial candidates

| Existing repetition | Possible mechanism |
| --- | --- |
| Stack offsets, widths, address equalities and alignment | Small arithmetic lemmas with controlled normalization |
| Stores preserving unrelated reads and mapped words | Frame/read-preservation lemmas and mechanical side-condition discharge |
| Register updates and callee saves | Controlled simplification of concrete register operations |
| Append/dropLast, endpoints and observer histories | Shared history properties and small composition procedures |
| Literal instruction-PC and cut exclusions | Kernel-checked computation over the existing instruction lists |

Start with address and memory-frame examples, then assess history bookkeeping.
Generalising duplicated peer-get proofs is a larger candidate only if simpler
replacements establish useful leverage. Heap predicates, alias/lifecycle
arguments and semantic loop invariants are not presumed automatable.

## Evidence and stopping criteria

Per retained pattern, report instances replaced, distinct contexts, net
handwritten proof-line change including library cost, manual side conditions
and exceptions, and observed elaboration/kernel replay cost. Distinguish code
factoring from tactic automation. Generated proof size alone is not the goal.
A large opaque tactic that barely reduces the tree is not success.

The strongest result is a formerly tedious proof reduced to a short ordinary
application, reused on another existing example with little adjustment.
Headline/type and trust-surface equality must hold; do not update their
expected specification to accommodate a refactoring drift.

[AGENT 2026-10-16] Use short measured rounds, initially targeting a few focused
hours rather than another milestone-length build. Reassess after each family.
Stop when remaining examples need semantic redesign, bespoke exceptions
outweigh common structure, checking/search cost outweighs source savings, or
successive candidates offer little net reduction. Report rejected candidates
and the reason. A smaller useful library is preferable to filling the list.
The stopping decision belongs to this agent; do not ask the user to enumerate
every pattern or keep working merely because more code could be factored.

## Validation and isolation

All builds and checks run through `capped`, with normal full Lake parallelism.
A KILLED banner or timeout is failure. Use private `.lake`, `.tmp` and a private
local clone of the exact clean Kraken pin; old worktree caches are read-only
inputs if copied. Do not mutate the paused branch or another agent's outputs.

Establish a baseline build/check, then use scoped checks during replacements.
At a retained-result checkpoint, run the existing binary proof gate, its exact
trust-surface diff, and scoped kernel replay of changed proof closures. No new
gating infrastructure. Source-only proof refactoring does not need fresh QEMU
coverage, oracle changes or mirror tests. Record existing external acceptance
as historical; request a fresh export gate only at an actual proof claim point
requiring it, with exactly the changed exported modules identified.

Keep temporary timing/export artifacts in `.tmp`; commit conclusions and
reproduction commands here, not giant logs or dumps. Record the final branch,
commits, retained mechanisms, measurements and stopping decision. Main remains
unchanged until separately authorised.

## Progress

The worktree is created at the fixed checkpoint. Pattern discovery has found
repeated modular stack-alignment arguments and repeated call-push frame
proofs across M1, the allowed-IPs port and common_bits. No replacement or
speedup is claimed yet.
