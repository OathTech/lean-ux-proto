# Goal: example-driven binary-proof refactoring

[USER 2026-10-16] Create a separate branch/worktree from the paused binary
checkpoint, record this framing, and begin the find–factor–replace–measure
loop. Build reusable mechanisms by shrinking existing M1 and completed M2
proofs; retain their highest-level proof structures. Exercise judgment about
lemmas versus tactics and stop when further work has diminishing returns.
This experiment should be substantially shorter than the initial proof build.

## Current direction

[USER 2026-10-16] Plan a sequential relational proof as a sibling to M1,
not a replacement. Correspondence points are freely chosen proof devices,
not the observations used to validate the mirror. Prefer stripping useful
M1 proof components to rebuilding everything; some invariants remain useful.
The deliberately unrealistic sequential model is an experiment in proof
cost, not a claim of composition into concurrent kernel contexts.

The sibling sequential lookup experiment is implemented; its result and
limitations are recorded below. The earlier rounds remain historical results.

The proposed next experiment has a separate
[build plan](2026-10-16-plan-executable-binary-correspondence.md): develop
executable reconstruction and loop assertions through paired Kraken/mirror
runs, then prove the tested definitions. That implementation has not started;
the results below remain the completed baseline.

## Fixed target and scope

Worktree: `.worktrees/binary-proof-refactor`. Branch:
`task/binary-proof-refactor`. Baseline: `6812d04`. The original
`.worktrees/binary-tv` remains paused and unchanged. Its incomplete M2 theorem
is not an objective of this experiment.

The existing proofs supply concrete examples and the regression suite. Keep
the existing M1/M2 headline statements, Pre, R and trust declarations fixed.
Keep the executable mirror, oracle, Kraken semantics and pinned dependency
commit fixed. The earlier refactoring rounds preserved their highest-level
proof structures. The sibling experiment adds its own explicitly weaker
statement and relations; it does not replace or weaken those existing claims.
This is not a campaign expansion or state-split migration. No merge to main,
no push, no global configuration or shared-cache changes.

The charter's direct-proof method remains: no certificate checker, no new
axioms, no native reflection axiom, no sorry or unsafe proof escape. Generated
proofs or tactic applications must be accepted by the ordinary Lean kernel.
The three preserved `.lean.draft` files remain outside the build and outside
all acceptance claims.

## The working loop for the earlier refactoring rounds

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

## Initial candidates for the earlier rounds

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
Existing headline/type and trust-surface equality must hold; do not update
their expected specification to accommodate a refactoring drift. The sibling
experiment has a separate, visibly weaker statement, as specified below.

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

## Sibling sequential relational proof

### Question and explicit limitation

How much cheaper is a function-level binary/mirror proof when execution is
sequential and correspondence points are chosen solely to simplify the
relational argument? This is an **unrealistic sequential-kernel experiment**.
It does not establish contextual refinement for concurrent Linux, justify
atomicity in Linux, or settle the eventual kernel observation interface.
M1 already uses a largely serialized environment; the main experimental
change is removing its internal observation/cut correspondence obligations.

Call the measurement an optimistic cost baseline, not a rigorous lower bound
on proof effort. Existing instruction facts, invariants and knowledge of the
completed M1 make this cheaper than an independent first construction.

### Target and sibling contract

[AGENT 2026-10-16] Start with `wg_index_hashtable_lookup`, including its bucket
loop and peer-get paths, because completed M1 supplies the closest control.
Prefer a stripped derivation using M1's useful physical region proofs, heap
predicates and loop facts. Introduce new proof modules/names for the sibling;
keep M1 and the incomplete M2 available unchanged. A helper-only pilot may
test the approach but is not completion of the lookup experiment.

Keep the existing lookup entry domain and accepted-mirror-run restriction.
Do not exclude dead peers, NULL words, collisions or legitimate aliases to
simplify the sibling. Preserve the existing concrete entry witnesses. Any
additional environmental premise must be stated explicitly in the sibling
statement, not hidden in a relation or a service lemma. Reuse existing named
service contracts and list the ones used; no assumed region correctness,
future readiness or termination premise may replace a proof obligation.

The sibling contract should relate ABI inputs and abstract state at entry,
execute the actual binary without interference, and establish the matching
return value, output word, relevant final abstract state, restored ABI and
endpoint memory footprint. Final service-state facts needed for another
sequential call remain explicit. Preserve Kraken's permitted instruction
outcomes and actual service executions/contracts; this is not a single
recorded-path test or deletion of synchronization instructions from the image.

Define a separate endpoint relation/observation projection for this contract.
Exclude exact internal decision logs and raw execution histories from its
observations. Persistent mutations still matter where they affect future
calls: clearing an owner's peer word cannot be abstracted away merely because
the store is internal. State precisely which final fields and effects the
sibling preserves, and derive its entry relation from the existing Pre.
Generic transport, if stated, is over that projection, not every predicate on
the mirror's instrumented trace. No concurrent-composition claim is made.

### Proof method

Use relational Hoare judgments of the form `{R_i} B_i ~ M_i {R_j}`. The
relations may differ by correspondence point. Binary and mirror fragments
need not take equal numbers of steps; silent fragments may stutter. Entry
and return implement the sibling contract, while intermediate points are
chosen for convenient alignment, not inherited from the recorded decisions
or the image's instrumentation cuts.

1. Write the sibling statement and identify the M1 obligations it omits.
   Choose candidate points around naturally aligned effects and a relational
   invariant at the bucket-loop header. Audit which M1 facts remain useful.
2. Strip a region with a pending update into a relational segment whose exit
   follows the corresponding updates on both sides. Check whether the
   pending-count/owner relation disappears. Retain it only if the new argument
   actually needs it; do not assume that every historical invariant vanishes.
3. Compose the loop and the null/dead/live paths using those segment facts,
   ending in the sibling function theorem. Reuse physical execution, memory,
   separation and ABI lemmas wherever they fit. Avoid rebuilding instruction
   proofs solely to obtain a cosmetically independent source tree.
4. Report the actual proof dependencies and remaining difficulties. A weaker
   corollary of M1 may serve as a specification reference, but simply projecting
   the completed M1 headline is not the construction-cost experiment. Reusing
   a helper theorem is allowed; disclose any fine-grained machinery it brings
   along instead of counting that machinery as eliminated.

No new general framework or tactic is a prerequisite. The earlier segment
prototype is optional: its preservation of every old cut must not determine
the new proof's granularity. Binary-only invariants inside a segment remain
available, as do useful intermediate relational assertions.

### Measurement, validation and stopping

Record construction elapsed time, build/check waiting time and significant
contract/invariant revisions prospectively. Distinguish reused work from new
work. Compare against M1 by obligations and dependency groups: physical
execution, heaps/separation, ABI/services, relational alignment, histories and
phase handling. Count new/adapted code and retained dependencies, not deleted
lines: the original proof remains present. Separate logical proof dependencies
from incidental module imports. Do not infer a campaign-wide speedup from a
warm build or a weaker statement's shorter source.

Use the existing binary gate to guard M1/M2 against drift. Print the sibling
statement, its explicit hypotheses and its axioms, and replay its actual proof
closure with the toolchain checker. Use the existing export-based external
gate at the appropriate claim point; local replay is not external acceptance.
No new gate infrastructure or change to the original expected surface is
needed for this experiment. All heavy work remains capped.

Stop after one complete sibling function and its comparison report. If the
small segment pilot does not simplify the alignment obligations, reassess
before expanding it into another lengthy proof family. An unfinished sibling
or a projection of M1 is reported as such. The result should tell us whether
relaxing the observation discipline removes the expensive obligations, and
which remaining costs merit tooling. Runtime testing of candidate relations
and a realistic concurrent observation model remain separate later questions.

## Sibling sequential experiment: result

[USER 2026-10-16] Run the sibling sequential experiment described above.

[AGENT 2026-10-16] Retain one complete sibling lookup proof and stop this
round. It demonstrates simpler relational composition without changing M1;
expanding the experiment into another bucket-loop implementation or a general
framework would measure a different intervention. The remaining physical
bookkeeping is substantial, so this result does not justify projecting a
campaign-wide speedup.

### What checked

`Binary.Sequential.lookup_simulation` in `binary/SequentialLookup.lean`
executes the actual image under `instructionStep` from the original
`Pre_lookup` to its original ABI return. It includes arbitrary collision
chains, the wrong-kind stop, NULL owner words, dead peers and accepted live
counts. The entry domain and accepted-source-run restriction are unchanged.
The live output may still alias disposable helper scratch; mapping is proved
using the existing bytewise lemma rather than a new separation premise.

The new `Post` exports the return value, live output word, restored ABI,
`Related` at return, memory footprint, coverage invariant, restored preempt
count and conditional softirq-pending word. `related_entry` derives the new
relation from the original Pre. `Post.frame` frames arbitrary memory
interpretations insensitive to the proved writes. This is not new transport
of the campaign's whole-operation results.

`Related` uses the existing bucket/owner/count projection of World, with a
new `At` predicate over ordinary current bytes. It has no execution history,
source decision log, pending count or pending owner clause. Both sides commit
the peer update before the helper-return correspondence point; both commit
the owner update before the result-region exit. Thus the dead path retains
its zero-count peer and clears the owner's peer word, including the original
alias cases. We did not alter the mirror to make the proof close.

Composition uses existing `Eventually` transitivity and physical execution
lemmas. No new search tactic, certificate checker or trusted automation was
needed. The nine sibling modules add **1,318 lines**; no existing proof was
deleted or replaced in this round. Some physical preparation proofs are
copied/adapted into the sibling. That duplication is appropriate to this
comparison, not a proposed long-term library design.

### Contract difference and realism

[AGENT 2026-10-16] The sibling's headline is an endpoint theorem of sequential
Kraken `instructionStep`; it does **not** export M1's `RunEnvironment`
permission audit. Its hypotheses do not include unused `SerializedEnvironment`
or `InvocationPermissions` arguments. This is a further explicit weakening,
not a proof that permissions or concurrency are unimportant. The original
headline and its audit are unchanged. Compare the sibling with M1's core
`lookup_kraken` as well as its audited headline so that deleting this audit is
not credited as an observation-alignment saving.

Sequentiality is inherent in this execution relation: no other CPU, interrupt
or external action is interleaved. Kraken's permitted undefined instruction
outcomes remain universally quantified. Real callback instructions and BH
instructions still execute under the existing named service contracts.
`instructionStep` does not independently discharge memory access permissions;
the sibling makes no claim about that audit or real Linux atomicity.

The named hypotheses are the unchanged `AnchoredDecoderAgreement`,
`TracePcContract`, `TraceCmp4Contract`, `TraceConstCmp4Contract`,
`TraceConstCmp1Contract`, `BhEnableContract`, `Pre_lookup`, and acceptance of
the executable `indexLookup` run. No region correctness, future readiness or
termination hypothesis was added. `TrustBase.lean`, the original expected
surface, image, oracle, mirror and Kraken pin are unchanged. No permission
premise is hidden as a fact of the Kraken model.

This does not settle Linux's contextual observation interface, prove
concurrent refinement, discharge the five service contracts from the image,
establish realistic entry reachability, transport whole-operation properties,
or complete M2. The existing witnesses were preserved, not rerun under QEMU;
there is no new differential-test or external-export acceptance claim.

### What became cheaper, and what remained

The new function proof does not depend on the completed M1 lookup theorem,
its selected/miss execution theorems, its helper simulation, its result
simulation or its common-finish theorem. It composes new endpoint proofs.
The selected suffix no longer proves matched source lists, cut alignment,
per-cut frames, pending-owner transitions or per-decision peer-count
correspondence. Those are concrete removed obligations, not just a shorter
spelling of M1's theorem.

However, this is a stripped proof, not an independent construction. The
entry/header/bucket loop and helper CALL still reuse M1's stronger proofs.
The bucket loop's invariant is composed through `bucket_from_head`, not
reproved under the weaker relation. The physical peer entry/return lemmas
still retain histories, scanner summaries and cuts internally. In particular
`PeerCountPhase.scan`, `countPhase` and `ownerPending` remain in the logical
closure. `owner_pending_result` and the all-cut peer execution theorems do
not. Empty-history bridges reuse ordinary physical frame lemmas; they do not
introduce a pending update into the new relation.

Stack save/restore, byte separation, coverage readiness and output mapping
remain most of the adapted suffix code. The experiment removes a layer of
alignment work; it does not make memory/ABI/service composition disappear.

A transitive traversal of declaration **types and proof/definition values**
(including opaque values and inductive constructors), not just imports, gives:

| Measure | M1 audited headline | M1 core before audit | Sequential sibling |
| --- | ---: | ---: | ---: |
| Referenced binary declarations | 1,694 | 1,636 | 1,462 |
| Binary modules containing those declarations | 154 | 152 | 130 |
| Lines in those whole module files | 22,789 | 22,491 | 19,928 |

The sibling shares 121 modules with either M1 closure, adds nine, and avoids
31 of the core's modules. The core-to-sibling declaration reduction is about
10.6%. Whole-module line counts include declarations unused by the theorem;
they are a coarse footprint, not proof-term size or lines saved. Imports
still bring in more modules than these logical closures. No speedup follows
from these counts alone.

The dependency traversal was an ephemeral measurement, not a new gate.
Reproduce by importing `SequentialLookup`, `LookupAdequacy` and `Lean`,
walking `Environment.find?` from each headline through
`ConstantInfo.type.getUsedConstants`, `ConstantInfo.value? true`, and
inductive constructors, deduplicating names, and mapping each name through
`Environment.getModuleIdxFor?`. The core is the private declaration
`_private.LookupAdequacy.0.Binary.LookupRelation.lookup_kraken`. Count only
modules with a corresponding `binary/<module>.lean`; include complete files
only for the explicitly labelled whole-module line measure.

### Time, failures and validation

Timing marker: **2026-10-16 02:07:49 UTC** at baseline `cc29454`, before the
first sibling implementation. There was a little source inspection before
that marker. The first successful complete sibling build ended at
**02:22:33.694 UTC**, **14 minutes 44.7 seconds** after it. This includes
adaptation and compile repairs, but excludes later dependency analysis,
reporting and fresh replay. It is a single-agent, warm-cache, heavily reused
construction; it is not comparable to M1's 16.98-hour first construction.
There is no independent new-function authoring-rate measurement.

The final scoped build took 0.93 seconds, maximum RSS 1,724,940 KiB. The full
binary gate passed all 544 jobs, the original exact headline/trust diff and
clean Kraken pin `7ebba06a30eaf08c10b26b28ca14bfee1c791576`; its warm run took
1.91 seconds, maximum RSS 1,770,060 KiB. Aggregate build waiting was not
continuously instrumented, so no total waiting-time estimate is claimed.

Failed intermediate builds were failures: option/integer coercions in the
peer result, dependent-match normalization in the endpoint relation, an
uninferred conjunction and missing local name in the helper adapter, and
the generic XOR lemma name/PC normalization in the clear tail. A temporary
source-extraction command failed before writing files; a dependency query
initially used invalid syntax for a private declaration name. All were
corrected before the successful runs. No failed run counts as validation.

The sibling headline, its miss/selected compositions, entry relation and
frame theorem report only `propext`, `Classical.choice`, `Quot.sound`.
Fresh aggregate replay **PASS**: `leanchecker --fresh RefactorReplay`,
108.13 seconds, maximum RSS 2,348,400 KiB, exit 0. Its complete imported
closure was replayed from an empty environment. No cap kill or timeout
occurred. This is local kernel replay, not external export acceptance.

Reproduce from the worktree root with `capped -- lake -d binary build
SequentialLookup` and `capped -- scripts/proof-gate --binary`. The aggregate
recipe below now includes all 56 changed/new modules since `6812d04` plus
five existing headline/witness roots, for 61 roots. From `binary/`, compile
that aggregate with `lean --root=../.tmp` and run
`capped -- lake env leanchecker --fresh RefactorReplay`. This is local kernel
replay; the user's external acceptance at `430ea90` remains historical.
For an external check of the sibling, export `SequentialLookup` (and the
original headline/witness roots if checking the combined branch) with
`leanexport`, then run `lake check --from-export` outside Nono as documented
in `binary/README.md`.

## Earlier follow-on: execution segments as the unit of proof

[USER 2026-10-16] Try the larger experiments discussed after round 3, with
execution segments as the highest-priority unit: start from a state
establishing the simulation relation, execute to a correspondence point,
and reestablish it. Update this plan and implement the experiments. Runtime
testing of candidate relations is an exploratory idea, not a required proof
mechanism or a replacement for proof.

[AGENT 2026-10-16] The previous stopping assessment applies to small local
substitutions only. It did not test the cost of region composition. Resume
on this branch from `7cebabd`, with one vertical example driving the API.
A segment may have internal cuts and callback states: endpoint R alone is
insufficient for the existing headline. Retain actual Kraken execution,
all undefined outcomes, the same accepted source run, and correspondence at
all required emitting points and cuts. Internal physical segments can carry
a component invariant; lifting/composition must supply the full unchanged R.

The experiments, in order:

1. **Complete callback argument.** Generalize the actual CALL/service/RET
   proof, including readiness restoration, return-word preservation,
   footprint and observations. Instantiate for M1 index lookup and its
   allowed-IPs peer context. Context laws must be proved from existing facts,
   not added to Pre, R or TrustBase. Count instance and library costs.
2. **Execution segment and loop composition.** Build a small proved segment
   interface that composes execution, endpoints, observations, frames/cuts
   and scanner facts. Use it for M1's callback-and-next-node step and carry
   the step through the existing bucket induction. The composition theorem
   must actually discharge obligations at joins, not merely package a long
   conjunction. Preserve the existing function theorem and path structure.
3. **Binary footprints.** Where that example still exposes repeated
   obligations, derive local read preservation and separation from known
   write footprints and interval inclusions. Normalize modular addresses
   with proved lemmas. Add a bounded tactic only if ordinary applications
   remain repetitive. Existing aliases remain permitted; unresolved alias
   cases remain visible. Do not strengthen global allocation assumptions.
4. **History summaries and reuse.** Carry reusable summaries of observations
   and scanner state, with proved links to the existing full-history
   computations and required prefixes. Test the mechanism on a completed M2
   component not used to design it; `common_bits` is the initial held-out
   candidate. This must not complete the unfinished M2 function theorem.

Use each experiment's failures to revise the smallest interface needed by
the next example. Success is lower cost for the next region/caller: fewer
bespoke join obligations, no parallel physical-proof family for a new
context, and preserved statements under kernel replay. Record library,
instance and call-site code together, compile/replay cost, and residual
manual obligations. Do not infer campaign throughput from line counts.
Stop a mechanism when its instances merely reproduce the old proof or it
requires function-specific hypotheses of essentially the desired result.

### Optional: runtime testing of relation candidates

There is value in using concrete machine/mirror states at cuts to falsify
an invariant candidate before investing in a universal proof. Keep this a
separate diagnostic experiment, deferred until the segment interface has a
concrete use for it. Prefer executable physical clauses and supplied finite
representation witnesses, preserving the distinction between physical
state, recorded environment and history. Missing observations or abstract
fields must yield an explicit unsupported/unknown result rather than pass.

A diagnostic success establishes only the tested instance. It cannot justify
universal separation, arbitrary heaps, absent readers, or closure under all
Kraken outcomes. A candidate check is not a certificate checker on the proof
path. If later used as a precise implementation of a relation clause, its
relationship to that clause would itself need proof. No new gate, oracle
instrumentation or executable-mirror change is part of this round.

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

### Round-3 stopping assessment (superseded for the follow-on)

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

### Round-3 kernel replay and reproduction

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


### Follow-on results: callback and execution-segment experiments

[AGENT 2026-10-16] Retain the shared callback proof and the small segment
prototype on this experiment branch. Stop this round before a wider interface
migration: the prototype checks, but has not demonstrated a reduction in
composition effort. Keeping it here makes that result reviewable; it is not
an instruction to convert the campaign to this API. No new search tactic is
justified by these examples.

The callback experiment uses `Instrumentation.call_return` in
`CallComposition.lean` for M1 lookup, the allowed-IPs peer context and the
held-out `CommonBitsCoverage.call`. It executes the actual CALL, composes the
existing service theorem, restores the caller stack, preserves the mapped
return slot and joins the write footprints. An arbitrary service
postcondition retains each context's actual observations and history. The
service theorem remains an argument supplied by the existing named contracts;
this work does not prove those contracts from the image.

`CallbackReadiness.lean` factors the same eight physical readiness fields and
their restoration for the first two contexts. Coverage state and eligibility
remain context-specific, with exactly the original byte separation premises.
Common_bits retains its distinct readiness record and supplies an adapter for
its local-history theorem. The held-out use therefore establishes reuse of
the CALL/return argument, not interchangeability of all callback interfaces.

`ExecutionSegment.lean` supplies two layers. `SegmentTrace` retains the
endpoint frame, the observer's result on the actual history, its last state,
and the invariant at every appended cut. Its composition and suffix lemmas
replace the two physical scan trace implementations. `Segment` additionally
requires actual Kraken `Eventually (historyStep fetch)` execution;
`Segment.bind` composes that execution and the audit together from the exact
returned machine/history. The audit composition law is proved by the caller,
not added as a binary environment assumption.

The bind is used twice: the callback followed by the next-node load in
`scan_miss`, and that segment followed by the recursive bucket search. The
original bucket induction and function headline are retained. At those joins
the shared lemma composes history extensions, cut frames, observations and
all-prefix scanner preservation. Heap-tail representation, read/write
separation, register/PC equalities and decision-to-source correspondences
remain explicit. These instances carry `StableTrace`, the physical component
of the invariant. They are not new uniform full-R segment theorems:
`LookupBucketSimulation` and the later unchanged proofs still perform the
lift to R and correspondence at emitting occurrences.

Line accounting against `7cebabd`, including all new Lean library code,
imports, adapters and downstream repairs:

| Experiment | Before | After | Net change |
| --- | ---: | ---: | ---: |
| Callback/readiness, ten modules including two new | 954 | 948 | -6 |
| Segment/trace, eight modules including one new | 1224 | 1272 | +48 |
| Follow-on total | 2178 | 2220 | +42 |

The callback library costs 91 lines and replaces 97 lines elsewhere. The
segment library costs 83 lines; the two trace implementations lose 48, while
the loop use sites add 13. This is a mixed outcome: shared correctness
arguments, little callback source saving, and a segment interface that still
costs more than its current replacements. There is no measured authoring-rate
or campaign-throughput improvement. Cumulatively with the first three rounds,
the branch changes 47 Lean modules and removes 701 net lines from `6812d04`;
that larger reduction still comes mainly from the earlier local refactorings.

**Footprint trial rejected.** A checked trial of modular subrange inclusion
and width weakening replaced six arguments across `LookupFromPre`,
`LookupHelperSeparation` and a held-out allowed-IPs live-entry proof. Including
the 21-line library it grew 528 lines to 547 (+19). It left the important
allocation/read-set arguments intact. Removed the trial and its Lake root;
no extra alias restriction, precondition or footprint tactic remains.
Existing `EqualOutside.loadInt`, `BucketShape.frame_reads` and allocation
facts already do the substantive work at the tested joins.

**History-summary result is limited.** The segment uses the existing proved
`StableExtension` summary, including every executed prefix, rather than
replacing full histories with assumed endpoint facts. Common_bits already has
`Local.trans` and `chain` for its local-history representation. This round
reuses the callback proof there but does not replace that composition or add a
new scanner-summary calculus. Runtime testing of relation candidates remains
deferred as described above; no runtime checker was implemented or validated.

The next meaningful success criterion would be a new region or caller that
uses a common interface without reintroducing cursor/annotation adapters and
per-point lifting. These trials do not establish that merely wrapping existing
conjunctions in a segment record achieves it. They also do not settle whether
a broader, consistently applied segment interface would pay off. Such a
migration is beyond the retained two-join prototype, not an achieved saving.

Validation: the full binary build passes (535 jobs). The binary proof gate
passes, including the exact original headline/trust declaration diff and
clean Kraken pin `7ebba06a30eaf08c10b26b28ca14bfee1c791576`.
The final gate invocation, including incremental rebuilding, took 7.44 seconds
(maximum RSS 1783996 KiB); it is not a before/after performance comparison.
The six new helper theorems' axiom reports contain only `propext`,
`Classical.choice` and `Quot.sound`.

Failed attempts were failures: readiness aliases required explicit unfolding
of `Context.Separated` at existing simplification sites; the shared trace
record required an explicit `ScanCuts.append` application where projection
inference lost its old name. Those integrated builds failed until repaired.
The footprint trial initially failed from an uninferred width and a concrete
address normalization, then checked before being rejected on cost. An
aggregate command initially used the root worktree instead of `binary/` and
failed before compilation; the corrected invocation succeeded. No failed run
is counted as validation.


Fresh kernel replay **PASS**: `leanchecker --fresh RefactorReplay`, 102.02
seconds, maximum RSS 2346576 KiB, exit 0. The aggregate imports all 47
changed/new Lean modules since `6812d04` plus `LookupSnapshotTransport`,
`LookupWitness`, `LookupHitWitness`, `AllowedipsCallerExecution` and
`CommonBitsExecution` (52 import roots). Its full imported closure was replayed
from an empty environment. Reproduce with the round-3 commands above; their
diff-based module enumeration now includes the follow-on modules. For the new
helper axiom reports append `#print axioms` for
`Binary.Instrumentation.call_return`, `Binary.CallbackReady.restore`,
`Binary.CallbackReady.congr`, `Binary.SegmentTrace.trans`,
`Binary.SegmentTrace.of_suffix` and `Binary.Segment.bind` to the temporary
aggregate before compiling it. No cap kill or timeout occurred. This is local
kernel replay, not a new external `lake check --from-export` acceptance.

Plan commit: `0d36fe8`; this results section and the prototypes land together
in the following experiment commit. The paused `task/binary-tv` stays at
`6812d04`. The mirror, Pre/R declarations, oracle/image terms, TrustBase and
Kraken are unchanged. There is no new milestone-2 completion, external gate,
QEMU/differential result, merge or push. Remove this round's temporary logs,
aggregate and rejected footprint build outputs after committing the result;
keep the private branch and normal build caches for review.
