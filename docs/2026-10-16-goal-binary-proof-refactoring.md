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

### Round 1: stack alignment and CALL entry

[AGENT 2026-10-16] Retain two ordinary lemmas: `Binary.aligned_sub` in
`binary/WordAlignment.lean` and `Binary.Instrumentation.called_entry` in
`binary/CallHistory.lean`. No tactic is needed for either property.

The first closes the modular alignment arithmetic, including wraparound;
the second establishes the pushed return word and aligned ABI frame without
a coverage-context hypothesis. Replaced 26 alignment arguments across 23
modules, with six of those sites subsequently using the CALL-entry lemma.
The six CALL sites cover M1 instrumentation, index lookup and peer calls,
the allowed-IPs versions, and common_bits. Nested prologue offsets use two
lemma applications. Register-argument setup still has its explicit local
simplification; no semantic exception or added premise.

Net Lean source reduction is **59 lines**, counting the new 14-line module,
CALL lemma and added imports. Original theorem signatures are unchanged.
The integrated build passes (530 jobs); the binary proof gate and exact
trust-surface diff pass. Scoped `lake env leanchecker MODULE` replay passes
for all 24 changed/new proof modules (24.51 seconds combined). This is
replay from imported environments, not a new external export acceptance.

Warm, single-run direct elaboration observations, in seconds:

| Module | Before | After |
| --- | ---: | ---: |
| CallHistory | 0.910 | 0.799 |
| CommonBitsEntryState | 0.973 | 0.838 |
| AllowedipsEntryContext | 0.870 | 0.753 |

These short shared-host measurements establish no regression at this scale;
they are not a reliable campaign-throughput speedup. The original warm gate
was 1.88 seconds, the new warm gate 1.89 seconds. The alignment rebuild's
86.29 seconds includes invalidated dependents and is not comparable to a
warm gate. Timings use `time.monotonic()` around `lake env lean MODULE.lean`
with no output object requested, under `capped`.

Setup failures: the first baseline gate lacked the new worktree's generated
Lake manifest; `lake -d binary update` resolved its local path dependencies,
and the rerun passed. An exploratory `leanchecker --help` invocation failed
because this executable has no help mode and tried the absent default
`BinaryTV` module; explicit module invocations passed. Neither failure is
counted as proof validation.

Reproduce from this worktree with `capped -- scripts/proof-gate --binary`;
from `binary/`, use `capped -- lake env leanchecker MODULE` for each module
changed by this round and `WordAlignment`. No expected trust-surface file,
TrustBase declaration, headline, Pre, R, mirror or dependency pin changed.

Rounds 2 and 3 below retain the literal layout iteration and the
repeated history-tail property. Trial copies and logs are ephemeral.

### Round 2: literal instruction-layout iteration

[AGENT 2026-10-16] Retain `binary_layout` in `binary/LayoutTactic.lean`.
This is a procedure over an existing concrete instruction list, not a new
checker, certificate or semantics. It applies `LaidOut.cons`, proves positive
length by ordinary `decide`, fetch equality by `rfl`, and monotonicity by the
existing `regular_mono`; only the smaller tail recurses. The empty-list case
uses `LaidOut.nil`. There is no broad simplifier or search through hypotheses.

Replaced **110** identical procedures: 54 in `ImageLayout`, 35 in
`AllowedipsLayoutProofs`, 21 in `CommonBitsLayout`. All original theorem
statements remain. There are no per-site side conditions or exceptions.
The first 54 are generated, so source savings must be separated: **320 net
handwritten Lean lines** (including the entire 16-line tactic module), plus
**324 generated lines**. `generate.py` also loses six lines and emits the new
invocation/import. Its layout-emission block reproduces all 54 declarations
exactly; the full ELF/DWARF generator was not rerun or modified otherwise.

One-off negative checks prove that the tactic fails for a missing fetch, a
zero-length instruction and a `.nop` outside `RegionOperation`, even with a
hypothesis of the desired layout supplied. They use `fail_if_success` and
are ephemeral, not a new gate. The first invocation used the wrong relative
`.tmp` path and failed before checking; the corrected invocation passes.

Integrated build PASS (532 jobs, 125.53 seconds including invalidated
imports); binary gate and exact trust-surface diff PASS. Scoped replay of
`LayoutTactic`, `ImageLayout`, `AllowedipsLayoutProofs`, `CommonBitsLayout`
passes, 8.09 seconds combined. Reproduce with the same gate and one
`capped -- lake env leanchecker MODULE` per named module in `binary/`.

| Direct elaboration, seconds | Before | After |
| --- | ---: | ---: |
| ImageLayout | 3.848 | 2.882 |
| AllowedipsLayoutProofs | 2.745 | 2.008 |
| CommonBitsLayout | 3.895 | 2.758 |

These are single warm shared-host observations, not controlled throughput
measurements. The `.olean` sizes increase slightly: 155152→155608,
127008→127312 and 87288→87480 bytes respectively, compared with the paused
baseline's objects. The demonstrated gain is shared source/procedure
maintenance, not smaller kernel proofs or a forecast for semantic composition.

### Round 3: history endpoints used in cut composition

[AGENT 2026-10-16] Retain the ordinary `Binary.history_restore` lemma in
`History.lean`. Its proof uses the existing list-library characterization of
`getLast?`; no list tactic or new history representation is needed. Ten
sites across index lookup, allowed-IPs/peer-get and service correspondence
now apply it. Existing public/local wrappers and high-level compositions
remain. The net reduction is **40 handwritten Lean lines** across nine
modules, including the shared lemma. No side conditions were added.

Integrated build PASS (532 jobs, 111.10 seconds including dependents);
final binary gate and exact trust-surface diff PASS (1.87 seconds warm).
Direct elaboration samples: `ScanFrame` 0.772→0.787 seconds;
`AllowedipsLoopFrame` 0.753→0.688 seconds. The small mixed changes reinforce
that these timings do not establish a campaign-wide performance claim.

### Stopping assessment

[AGENT 2026-10-16] Stop this bounded experiment after the three retained
rounds. The final inspection, informed by the note about the forthcoming
mirror state split, concentrated on binary histories, cuts, separation and
callbacks. Nothing here refactors the per-call mirror World interpretation
or mirror-side frames. This work should survive that split.

`storeInt_defined`, `EqualOutside.loadInt`, `InRange.offset_disjoint` and
`CutFrames.append_after` already capture important binary frame properties.
The witness store-preservation examples use short explicit iteration; giving
those another tactic name offers little gain. Many remaining frame weakenings
or equal-footprint compositions are one or two lines. The longer callback
proofs differ in coverage-context fields, footprint inclusions and scanner
invariants: factoring them deserves a new concrete example, not an expanding
search procedure in this first experiment. No general callback-interface
redesign or shared-region composition rewrite was attempted.

The retained library is **three proved lemmas and one structural tactic**.
Across 37 Lean modules, it removes **743 net lines**: **419 handwritten**
and **324 generated**, counting new library code and imports. The emitter
also loses six Python lines. This is measured maintenance leverage over
existing M1 and completed M2 components. It neither completes M2 nor resolves
the original campaign's function/trace composition cost. The largest source
reduction is repetitive layout boilerplate, not semantic invariant work.

Branch remains `task/binary-proof-refactor`, based on `6812d04`, with goal
commit `b453a2c`, lemma round `3fc7aad`, tactic round `da2c600`, and the
history/result commit carrying this final assessment. The original
`task/binary-tv` still points at `6812d04`. No merge or push was performed.
Headline declarations, TrustBase, Pre/R, mirror, oracle/image terms and
Kraken pin remain unchanged. No fresh QEMU or differential claim is made.

### Final kernel replay and reproduction

Fresh combined replay **PASS**: `leanchecker --fresh RefactorReplay`,
102.79 seconds, maximum RSS 2345332 KiB. The temporary aggregate imports all
37 changed/new Lean modules plus `LookupSnapshotTransport`, `LookupWitness`,
`LookupHitWitness`, `AllowedipsCallerExecution` and `CommonBitsExecution`.
Its entire imported closure was replayed from an empty environment. The
first aggregate compilation rejected a source outside the package root;
adding the explicit `--root=../.tmp` fixed that invocation before replay.
There was no cap kill or timeout.

`#print axioms` reports `[propext, Quot.sound]` for `Binary.aligned_sub`
and `Binary.history_restore`; `Binary.Instrumentation.called_entry` adds
only `Classical.choice`. The final gate still accepts the original exact
headline/trust declaration specification. This is local kernel replay, not
a fresh external `lake check` acceptance; the user's external acceptance of
commit `430ea90` remains historical.

Recreate the aggregate from the worktree root:

```sh
python3 - <<'PYCODE'
from pathlib import Path
import subprocess
modules = {Path(p).stem for p in subprocess.check_output(
    ['git', 'diff', '6812d04', '--name-only', '--', 'binary/*.lean'],
    text=True).splitlines()}
modules.update(['LookupSnapshotTransport', 'LookupWitness', 'LookupHitWitness',
                'AllowedipsCallerExecution', 'CommonBitsExecution'])
Path('.tmp').mkdir(exist_ok=True)
Path('.tmp/RefactorReplay.lean').write_text(
    ''.join('import ' + m + '\n' for m in sorted(modules)))
PYCODE
capped -- scripts/proof-gate --binary
```

Then from `binary/`:

```sh
capped -- lake env lean --root=../.tmp \
  -o .lake/build/lib/lean/RefactorReplay.olean ../.tmp/RefactorReplay.lean
capped -- lake env leanchecker --fresh RefactorReplay
```

The experiment's `.worktrees/binary-proof-refactor/.tmp` and temporary
`binary/.lake/build/lib/lean/RefactorReplay.olean` are removed after recording
these conclusions. The branch/worktree and private build caches remain for
review. No trial files, timing dumps, exports or logs are committed.
