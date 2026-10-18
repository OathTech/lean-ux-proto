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
