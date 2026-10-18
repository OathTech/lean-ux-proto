# Paired execution: complete-call and cost calibration increment

Status: implementation in progress on `task/binary-pair-runner`, starting
from `2edbc26`. This continues the
[executable correspondence experiment](2026-10-16-plan-executable-binary-correspondence.md).

## Purpose and decisions

[USER 2026-10-18] Continue the experiment on its existing branch, with a
detailed implementation plan and measurements that can establish whether
the workflow makes binary proof development affordable. Investigate new
sources of cost and mechanisms for reducing them as they appear.

[AGENT 2026-10-18] Use the complete sequential allowed-IPs call as the next
integration test, then a small previously unproved mutation as the first
new-code calibration. Keep generic tooling subordinate to these examples.
Preserve the original M1 result and the sibling's existing observations.
No mirror changes, merges, pushes, oracle changes or global configuration
changes are part of this increment.

The hypothesis is that executable reconstruction and assertions let us
discover missing invariants before expensive composition, and that their
proved consequences can be reused at segment boundaries. The hypothesis is
not that passing workloads proves adequacy, or that the earlier physical
proof cost disappears. We will record evidence against the hypothesis too.

## Baseline and intended statement

The existing `findNode_checked` theorem derives setup from the executable
`initialBoundary` and proves the nonempty trie loop, with a reconstructed
heap and a physical frame. Actual sequential IPv4 and IPv6 captures pass
the same checks. The existing physical entry, helper and tail proofs are
available for reuse. No complete allowed-IPs call theorem is claimed yet.

The complete-call target is conditional on:

- a successful executable call-entry assertion on the initial machine
  state and mirror state, with one identity interpretation;
- acceptance of the actual executable mirror lookup;
- separately named decoder and service contracts.

Its conclusion is eventual binary return to the original return address,
the corresponding peer result and reconstructed trie/count projection,
restored callee-saved registers and stack, and the reusable physical
coverage/preempt/pending state. Memory outside the call's write footprint
is framed. Source decisions and diagnostic histories are not observations.
The proof must execute every region; no execution oracle or future-state
premise is permitted in the entry assertion.

The scope remains sequential: capture defers interrupts and timers, and
the theorem makes no concurrent contextual-refinement claim. Source
refusals, including the current dying-peer retry, remain explicit failures
in the paired test and outside the accepted-source theorem. This does not
change M1's dead-peer coverage or its precondition. We will distinguish
empty roots, search misses, live hits, and refusals in the report.

## Work sequence

### A. Make complete-call readiness executable

Read the existing region contracts and collect their entry obligations by
purpose: ABI/input decoding, coverage metadata before and during BH
disable, pending softirq state, mapped stack, and separation from decoded
objects and callback writes. Inspect the actual deepest helper footprint;
do not inherit a convenient but insufficient loop-only stack bound.

Implement one fail-noisy call assertion and use it in both constructed and
captured runners. Check it on IPv4 and IPv6 before proving its inversion.
Add focused rejection cases for any genuinely new assertion class. Keep
semantic callback behavior out of the data checker. No second independently
supplied physical interpretation may enter the proof.

Deliverable: executed positive entry states and named failures for bad
inputs; a precise list of additional assumptions exposed by the envelope.

### B. Connect the call assertion to existing entry proofs

Prove decoder and separation consequences once, using small reusable
lemmas where the same argument appears. Derive the original entry-region
premises, execute the prologue and endian conversion, and establish the
checked loop boundary. Preserve ABI/return slots and the callback state
through the loop by its write footprint. Cover the empty-root path
explicitly rather than adding a nonempty-root requirement to entry.

Deliverable: a checked entry-to-search theorem with no future-state
assumptions. Measure time spent discovering assertions separately from
time connecting them to existing physical contracts.

### C. Reconstruct through mutation and close the return

Prove a reconstruction update lemma for a peer-count word. It must identify
the changed peer, preserve every decoded node and other count by separation,
and agree with the actual mirror update. Use it with the existing live
peer-get effect; retain the explicit refusal behavior for dying-peer retry.

Compose search, peer acquisition and return. Export the original return
address, restored ABI, reconstructed endpoint and callback metadata needed
by another call. Keep histories required by old lemmas internal. Avoid a
new tactic framework unless a repeated search procedure actually warrants
one; prefer ordinary lemmas for repeated facts.

Deliverable: the complete sequential call theorem and kernel-checked
non-vacuity witnesses; paired replay continues to use the definitions proved.

### D. Reduce measured execution costs

The baseline two-seed captured replays take 224.79 seconds (IPv4) and
215.61 seconds (IPv6), using roughly 6--7 GiB. Capture takes about 28 seconds.
These are single shared-host measurements, not stable performance estimates.

Profile the full-buffer readiness scan and memory construction separately
from execution and assertions. The leading candidate is a proved bounded
coverage-buffer requirement, but it changes physical readiness contracts:
derive a sufficient write bound and test it before replacing the old check.
Do not drop mapped-memory obligations merely to improve a benchmark.
Prefer a small representation or repeated-check optimization when it
preserves the current contract and costs less than changing the proof.

Deliverable: comparable before/after timings, peak memory, exact semantic
changes (if any), and a decision about whether repeated workload iteration
is now practical. A failed optimization is a recorded failure.

### E. Calibrate on genuinely new mutation

Once the complete call is established, select one small anchored mutation
without an existing physical proof. Inspect candidate index-table updates
and removals before selecting: choose a bounded change that exercises heap
mutation and identity while avoiding a hidden new concurrency claim.
Document the selected function/segment and why it is representative.

Develop reconstruction/assertions by paired execution, then prove the same
definitions. Count fresh instruction semantics separately from reused
lemmas, and record any remaining bespoke frame/composition work. This is
the first basis for assessing new-function cost; adaptation of paid-for
M2 proofs must not be presented as that measurement.

## Measurements and stopping rules

Record UTC start/end checkpoints and distinguish active investigation from
build/replay waits; where they overlap, report wall time without summing it
twice. Track assertion design/debugging, proof adaptation, fresh physical
proofs, composition, validation, and performance work. Report code size as
a secondary diagnostic, with reused dependencies explicit. Preserve failed
build/run outcomes in the report's conclusions, not giant committed logs.

For each mechanism, answer: what recurring obligation did it remove; which
two uses demonstrate reuse; what did it cost to build; and what remains
bespoke? Do not infer a campaign speedup from a single reused example.

Pause generic mechanism work when its next use is speculative, when it
duplicates existing infrastructure, or when the remaining cost is semantic
rather than bookkeeping. If the complete-call composition exposes a wrong
statement or abstraction, report the finding and revise the plan explicitly;
do not tighten entry to hide a valid case. The next report must say which
checkpoints are complete and which are open, even if calibration is negative.

## Validation and trust

All heavy work uses `capped`; killed or timed-out runs fail. Use the existing
three-way oracle comparison before paired function runs, reuse identified
recordings when appropriate, and keep captures distinct from constructed
heaps. Run the relevant model/build/unit checks before code commits.

For each new headline, print axioms and replay its closure with fresh
`leanchecker`. Only `propext`, `Quot.sound`, and `Classical.choice` are standard.
No `sorry`, native reduction axiom, unsafe proof path, or hidden service
axiom is acceptable. Prepare a leanexport of the headline/witness modules;
the external gate remains the user-run `lake check --from-export` outside
Nono. Local replay is not reported as external acceptance.

Keep one experiment row in the proof register and one results section here.
Record the mirror and Kraken pins and their lag. Keep artifacts under `.tmp`
ephemeral; commit implementation, conclusions and reproduction commands.

## Execution record

- 2026-10-18 03:37:17 UTC: baseline inspection began at clean `2edbc26`.
  Current cost category: contract inventory and executable entry assertions.

### Entry and search checkpoint (2026-10-18)

The first implementation connects `callBoundary` to the existing physical
`AllowedipsEntry` through `callBoundary_pre`, and executes the prologue,
endian conversion and BH-disable through `callEntry_checked`. The checked
facts use one interpretation from Names. The selected peer is computed
from the source trie; no positive-count premise is added. `search_segment`
then handles the empty-root edge or composes the root segment with the
previously proved trie loop. These are intermediate results; peer-update
reconstruction and the complete function join remain open at this point.

The reusable mechanism introduced here is `Covers`/`spansApart_disjoint`:
prove a finite cover of a byte footprint once, then turn its executable
range check into the byte-wise separation premises of existing regions.
It is used for decoder, stack, input, callback, count and preempt footprints.
The old entry relation is derived from reconstruction, including the
selected count. It is not accepted as a second independent assumption.

The executable entry check accounts for 18 stack words (144 bytes), both
callback phases, the actual ABI/query/return word, conditional pending
softirq state and the required separations. The metadata check was split
from the current preempt-word check so both phases can be checked on the
same initial memory. This preserves the loop's coverage contract. Proof
inversion exposed one additional header-separation case: KCOV's header is
read even when its capacity is zero, so separation cannot be derived from
membership in its data-write range alone.

Both captured calls passed the first version of the complete-call assertion
and returned with matching observations under both seeds. Measured replay
was 273.145 seconds (IPv4) and 263.299 seconds (IPv6), including the extra
full-buffer scans; the previous checkpoint measured 224.79 and 215.61
seconds. They ran concurrently on the shared host. This is evidence of an
iteration cost to investigate, not a controlled attribution of the increase.
Final replays after the diagnostic coverage fix also passed: 262.632 seconds
for IPv4 and 250.530 seconds for IPv6, with both seeds and all captured
controls. These are shared-host observations, not controlled benchmarks.

`CallWitness.check4` and `check6` prove that exact small initial states pass
`callBoundary`; `CallWitness.pre` derives their physical preconditions.
The `binary-pair-call-witness` executable runs those same definitions through
Kraken to return: IPv4 takes 652 instructions, IPv6 787, with both undefined
seeds. Each has one trie header and returns peer 0, incrementing its count.
These are synthetic witnesses, distinct from the captured calls.

That execution found a runner defect: the four-word witness buffer fills,
but the diagnostic coverage list previously counted every callback as a
stored record. The binary correctly stops recording at capacity. The paired
runner now uses the existing executable `KcovPlan` at callback entry to
record only callbacks that store a PC. Actual service instructions continue
to execute. The first exact-witness run failed at the return count check;
after this change all four witness runs pass. The existing constructed
suites still pass, including explicit dying-peer refusal. Three new controls
per family reject a missing deep peer-get stack byte, a changed return word,
and a wrong network-order input. Transport unit tests pass (2 tests).

The entry and search proof builds print only the three standard axioms for
their new headlines. A fresh replay of the entry/witness closure succeeded;
the combined search/witness fresh replay also passed at 03:55:46 UTC. One attempted multi-module
`leanchecker --fresh` command was rejected by its CLI: that flag accepts
one root module. `PairCallWitness` now imports the search proof to replay
both through one root. No external acceptance of this increment is claimed.
The accepted external export remains the one at `a33869e`.

The work began at 03:37:17 UTC. By 03:52:30 the entry checks, positive
witnesses, root/search composition and diagnostic fix built and the exact
witnesses had executed. This approximately 15-minute interval includes plan
writing, contract inspection, proof adaptation, failed elaborations and
concurrent builds/replays. It excludes final validation and reuses all
instruction-region proofs. It is not a new-function proof rate. A notable
portion of the proof iteration so far was conversion between register
views, stack coordinates and existing relation types; the range-cover
lemma reduces separation boilerplate but does not remove those conversions.

Reproduce from this worktree:

```sh
(cd binary && capped lake build PairCallWitness binary-pair-call-witness binary-pair-allowedips)
capped binary/.lake/build/bin/binary-pair-call-witness .tmp/binary-allowedips/input-5.json
capped binary/.lake/build/bin/binary-pair-allowedips .tmp/binary-allowedips/input-5.json
capped binary/.lake/build/bin/binary-pair-allowedips .tmp/binary-allowedips/input-8.json
(cd binary && capped lake env leanchecker --fresh PairCallWitness)
capped python3 -B -m unittest binary.test_allowedips_capture
```

Use the capture/replay commands in `binary/README.md` for independent
three-way checks and actual captured state replay. Mirror pin remains
`cb2348e`, lagging main `77c9b55` at this checkpoint. Kraken remains clean
at `7ebba06a30eaf08c10b26b28ca14bfee1c791576`.


### Complete sequential call (2026-10-18)

`Binary.Pair.Trie.lookup_checked` in `PairCallAdequacy.lean` now composes the
actual entry, root/search loop, selected-node test, peer-get and return tail.
The headline takes successful `callBoundary`, acceptance of the actual
`WG.lookup`, and named decoder/callback contracts. It concludes eventual
return with the corresponding peer, exact executable trie/count reconstruction,
callee-save/stack restoration, before/during coverage invariants, restored
preempt count, conditional pending-softirq word, and a byte frame outside
stack/coverage/preempt/count writes. It covers empty roots, search misses and
accepted live hits, in both families. The dying-peer retry remains an explicit
source refusal; no positive-count premise was added to entry or reconstruction.

The helper's mutation now uses three layers: `reconstruct_map_counts` for a
memory-independent decoder transformation; `reconstruct_peer_frame` deriving
unchanged node/other-peer reads from the physical write footprint and the
allocation checks; and `hit_segment` applying those facts to the actual
peer-get execution. Static name/layout/allocation validation was factored out
of `reconstruct` so a memory update does not require re-proving validation.
The byte mapping, pointer contents, source target and accepted layouts are
unchanged. `lookup_effect` derives the accepted mirror's live-hit arithmetic
bound internally. Diagnostic histories remain internal to reused lemmas.

`PairCallWitness.accepted` kernel-reduces actual mirror acceptance for both
exact entry witnesses. Their executable runs still execute 652/787 binary
instructions under both undefined seeds and return with the changed count.
Both constructed suites pass (9/10 structural cases, 20 controls per family,
including the explicit retry refusal). The transport unit tests pass (2).
`lookup_checked` and all added update/source/segment/witness headlines print
only `propext`, `Classical.choice`, and `Quot.sound`. Fresh closure replay passed, as did a second replay after the mapping-check
experiment. External replay is pending.

The complete headline first built at approximately 04:10 UTC, about 33 minutes
after the 03:37:17 start. This includes planning, assertions, witnesses,
composition and concurrent replay waits. Instruction-region proofs were all
reused. The roughly 1,600 lines in the call/update modules include executable
checks, witnesses and helper lemmas, not only the headline proof. Remaining
iteration was mostly adapting endpoint facts, address coordinates, finite-map
updates, and Lean elaboration (including choosing explicit arguments before
rewriting under a footprint). No new search tactic was needed. This supports
endpoint summaries as an effective interface for this example; it does not
measure fresh-function cost or establish campaign affordability.

### Runtime-cost experiment in progress

The replay executable now reports input parsing, memory loading and paired
execution/checking separately. The first IPv4 split spends 13.656 seconds
loading the captured 32 MiB allocation. A candidate optimization replaces
integer construction in mapped-word checks with byte-presence checks;
`mappedBytesCheck_eq` proves exact equality with Kraken load definedness.
The full allocation and every existing obligation remain checked. Both runs passed, but the optimization did not help: 256.55 seconds before
and 261.11 seconds after (paired execution/checking 242.171 versus 245.907
seconds; loading 13.656 versus 14.535 seconds). The candidate and its extra
proof were removed. These overlapping shared-host runs do not resolve small
differences, but provide no evidence of a useful gain. The initial witness rebuild failed because its concrete
reduction expected the old load expression; rewriting with the equivalence
lemma repaired it. This was a failed build, not a passing witness.

[AGENT 2026-10-18] Inspect index removal before replacement for the fresh-code
calibration. Removal exposes predecessor-link writes, optional successor
backlink repair and unlink state in a smaller body. The main new uncertainty
is reconstructing a structurally changed heap, rather than scalar arithmetic.
A complete allowed-IPs call is now available as the composition baseline.
