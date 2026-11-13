# Independent review of the binary remediation plan

Reviewed revision: `2c020e3192aafc60788d5f9b5da2df6088416737`.
Archive inspected: `8b498e7ec207a042540148dda5881787731b5ac0`
(`archive/whole-driver-pilot-2026-11-12`). References below use those
revisions; archive paths are explicitly marked.

Recommendation [AGENT 2026-11-13]: retain the staged approach and the bounded
first investigation batch, with the clarifications below. Do not treat
adoption as readiness to commission the later composition proofs. The plan
can produce useful local binary results; its most important remaining
ambiguity is which real caller behavior those results will actually prove.

## Findings

### F1 — High: state the caller-establishment obligation explicitly

**Plan:** lines 254–280 and 292–300, especially the instruction at 265–266
to record caller transitions as environment actions and the stage-5 exit
requiring witnessed hand-overs before proving composition.

Testing that an actual next entry satisfies its precondition is valuable,
but does not establish that the permitted caller transition guarantees
that precondition. A composed theorem can still quantify over each next
entry *assuming* its `Starts`, even after a complete successful capture.
That gives a conditional sequence of local calls, not a proof that the
selected caller executes that sequence correctly.

This is a concrete distinction in the archive. In
`binary/WDCompose.lean:27–38`, `Covered` assumes `e.Starts` afresh at each
invocation. Its proof at 69–79 carries the invariant forward and accepts
the next `starts` as an input; it does not derive it. Capturing a `Walked`
witness (145–157) establishes existence, not a universal caller theorem.
This remains true even with one heap and no invented ghost updates.

The plan's stated objective at 19–21 is stronger than that outcome. Before
stage 5 commissions a composition proof, require each edge to name the
actual caller/environment transition, the invariant and prior postcondition
it may assume, and the next entry condition it must establish. Classify
each edge as instruction-proved or assumed under a stated contract. A
sampled contract is still assumed. In stage 6, identify the in-scope
WireGuard caller instructions separately from external kernel services;
moving those instructions into the environment must reduce the advertised
claim. This requires a short statement obligation, not a new audit system.

### F2 — Medium: align the source replay with the binary function cut

**Plan:** lines 91–118 and 354–358.

The proposed source-prefix comparison is underspecified at precisely the
point where the existing helper stops too early. At current
`binary/ProbeSupport.lean:46–87`, `replayRecordedPrefix` executes only
completed syscalls and ambient work. `binary/pair_capture.py:64–66`
explicitly excludes the operation containing the selected call. Current
`binary/PairMutatorCapture.lean:106–113` compares that prefix to the function
entry, reports the difference, then constructs a source state from the
captured projection.

A difference need not be a mirror defect or an invalid relation: real
caller work may have occurred inside the current syscall. For example,
`Leanux/WG/Handshake.lean:279–296` creates and initializes a keypair and
runs `addNewKeypair` before `indexReplaceHandshake`; these operations can
change identities and the represented table before the replacement entry.
The pre-syscall state is not that call's source pre-state.

Require an independently executed source state at the matching function
cut, with the current operation's hidden records consumed up to that cut
and the remaining stream retained. State how that cut is obtained without
substituting captured heap values or rewriting the operational mirror for
proof convenience. If that capability is missing, report caller alignment
as unresolved and keep the local state-input theorem separate. Merely
turning the existing prefix comparison into a failing check would not
repair admission.

### F3 — Medium: distinguish admission-ready from proved-and-accepted exits

**Plan:** stage table at 45–51; stage-3 exit at 199–204; stage-5 exit at
275–280; acceptance procedure at 324–333.

The table promises a scoped proof in stage 3 and composition proofs in
stage 5, but their bold exit paragraphs first describe passing captures,
then say to begin the proof. This permits an ambiguous completed-stage
report when only admission has passed, or when local proof checks have
passed but external kernel acceptance remains pending.

Give these stages two named outcomes: admission-ready, which permits proof
work, and proved-and-accepted, which requires the actual theorem, its
stated universal assumptions, the applicable trust checks and the external
acceptance required by the existing rules. A stopped investigation or a
conditional local result should retain its own explicit outcome. Stage 1
already handles unresolved groups honestly; apply the same precision to
the later stage labels.

## What the plan gets right, and remaining feasibility risk

The distinction between universal service obligations and sampled service
instances is necessary. The current `RandomReturnContract` and
`RandomInputCoupling` in `binary/TrustBase.lean:718–759` quantify beyond a
captured draw. The proposed allocator transition boundary also avoids
pretending the archived `AllocatorContract` executes the real allocator
under the old ISA semantics. The source-copy repair is substantive:
archive `ParamCopyEq.lean:35–37` proves equality at `Models.mirror`, whereas
`WDAdapter.lean:222` defines a different, answer-fed interpretation.

Full native frame admission is still a feasibility question, not a result
of this review. Archive `RtC2Statement.lean:78–86` uses `EqualOutside`,
which quantifies over every address (`binary/Memory.lean:38–39`). Archive
`RtC2Captured.lean:81–89` builds a sparse state containing only the window,
nonce and preempt word; its own documentation at 21–23 excludes the native
frame. The plan correctly refuses to count missing bytes as preservation.
Its first C2 investigation should return a concrete observation domain and
frame-checking method, or an unresolved result; running that sparse-state
predicate again cannot meet the proposed stronger exit.

## Validation performed

Read-only source and statement inspection using `git show`, numbered file
reads and targeted searches: the plan and assessment; current register and
binary README; current lookup/transport and mutator capture definitions;
archive C2 statements, capture and sequence definitions; C1 service and
headline definitions; parameterized-copy interface; and whole-driver
composition/invariant definitions. The assessment's execution totals were
not independently reproduced. No build, guest capture, proof checker or
heavy experiment was run; the findings concern statement and plan
obligations, and none depends on a fresh kernel behavior claim. The review
document was checked with `git diff --check`. No implementation was changed.

## Follow-up on the revised proposal

Reviewed revision: `a616d1fe63c46e1554cbba29f7ca2ccae75cde24`.
Judgment [AGENT 2026-11-13]: the three findings above are addressed at the
plan level. I found no remaining material objection to adopting this
proposal and commissioning its bounded first investigation batch. This is
not acceptance of an implementation or permission to begin the later proof
phases before their admission conditions are met.

* **F1 addressed:** revised lines 328–337 require each prior result and
  permitted transition to establish the next entry, distinguish this from
  caller progress, and classify assumed edges. Lines 324–326 and 366–369
  keep in-scope WireGuard callers within the binary claim; putting them
  behind assumed contracts reduces that claim. Stage 5 now requires the
  classified edge obligations themselves to be proved (346–354). These
  requirements exclude the insufficient `Covered`-only outcome identified
  in the original review.
* **F2 addressed:** lines 122–132 require replay through the current syscall
  to the matching function cut, retaining the remaining input stream.
  Lines 155–159 preserve the legitimate local state-input claim without
  confusing it with independent caller admission. The first batch at
  445–448 investigates that missing observation capability rather than
  classifying an unaligned comparison as a mirror failure.
* **F3 addressed:** lines 61–68 define the distinct admission and proof
  outcomes, and stages 3–6 apply them. Pending external acceptance cannot
  be reported as a completed proof stage. Lines 408–415 additionally tie
  acceptance to the actual headline, meaning-defining predicates and
  export closure of each recovered result.

I also inspected the added complete-interval requirements at 182–211.
They are proportionate to a joined claim and preserve sampled captures as
diagnostics. The source supports the identified risk: archived
`binary/contracts/capture.py:494–508` can disarm sites and later emit
coverage summaries; `wd_trace.py:65–76` omits those summaries when producing
events. The revised plan requires checking this information before a join
is admitted. The proof-closure change likewise addresses the current
explicit lists in `binary/surface.py:10–89`, the top-directory source scan
in `scripts/binary-proof-gate:158–164`, and the nine documented export roots
in `binary/README.md:99–102`.

The important remaining uncertainties are feasibility questions that the
revised plan now reports honestly: observing a matching source cut,
admitting a native frame beyond sparse snapshots, recording a complete
ordinary-scheduling interval, and resolving any non-executable universal
premise. Lines 228–243 make the frame investigation's unresolved outcome
explicit. None of these capabilities was demonstrated by this document
revision; the bounded investigation must establish them or stop with the
declared narrower result.

Follow-up validation: read the revised plan, its diff and dispositions;
rechecked the relevant existing collector, event conversion, proof-surface,
gate and export definitions. No other review was used as settled evidence.
No build, capture, proof checker or heavy experiment was run. The appended
review passed staged `git diff --check`; no implementation files changed.
