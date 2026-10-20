# Independent review: paired index insertion

Reviewed on 2026-10-18 against `b22264a4`, branch
`task/binary-pair-runner`; proof/export source
`b3d57f17b3dbc3f47ade3feb3aa1322886461d2d`. The later commits are documentation
only. This review evaluates that checkpoint, before subsequent repairs.
The reviewer read the charter and working rules and independently inspected
the theorem statements, source reduction, retry composition, retained caller,
provider contracts, executable checks, capture path and reported conclusions.

**Verdict: changes required.** The general conditional insertion and composition
proofs are substantial results, but a concrete admitted provider state refutes
the physical service specification for the executable image (R1). Consequently
this is not yet an acceptable completed image-refinement checkpoint. A passing
Lean build or external export check cannot discharge that specification defect.
R2 is a separate replay-provenance defect. Neither finding is evidence of a
WireGuard kernel bug or a discrepancy in the actual Lean mirror.

## R1 — High: provider readiness permits internal aliases that invalidate its postcondition

Locations at the reviewed commit:

- `binary/RandomState.lean:48–58`, `77–94`, and `98–103`: steering and sequence
  resources are checked for mapping and current scalar validity, without
  separating their semantic roles inside the private memory cover.
- `binary/RandomReadyCheck.lean:27–31`: separation checks protect stack,
  callback metadata and buffer from private memory, but do not separate
  private structures from one another.
- `binary/TrustBase.lean:681–693`: `RandomReturnContract` universally promises
  a return preserving `RandomProvider.check` for each admitted service state.
- `binary/PairInsertAdequacy.lean:32` and
  `binary/PairInsertSequenceAdequacy.lean:103`: both headlines require that
  universal physical contract.

Starting with the existing direct-recording fixture, make its steering pointer
refer to four bytes before `sequenceAddress`. The steering count is then zero,
its head is the low half of the sequence counter, and its mismatch count is the
high half. All three are initially zero. Supply a mapped twelve-byte private
span there. The exact `readyCheck` accepts. The actual fetched random body
returns seven in 462 instructions, but increments the aliased sequence/head
to one. The required postcondition rejects `head=1, count=0` with
`random.private.steering-counts`.

The reproducer below replaces the original sequence span, so the declared
private allocation spans do **not** overlap. Merely rejecting overlapping
`Config.blocks` would therefore miss the defect. The necessary condition is
about the reads and writes of the private structures, not the way their byte
cover happens to be partitioned.

This is a counterexample to the *assumed physical service specification*, not
to the kernel-checked conditional implication. No input-coupling hypothesis,
desired insertion result, or fabricated service return is used by the test.
`RandomRun.execute` interprets `RandomImage.fetch` and `ServiceImage.fetch`.
The synthetic return address has no fetched instruction after return, so a
later caller execution cannot repair the failed service postcondition. No
kernel reachability of this synthetic alias is asserted; the contract's
present readiness domain admits it without a reachability premise.

Reproduce from `binary/`, without creating another source file:

```sh
capped lake env lean --stdin <<'LEAN'
import PairRandomRun
open Binary Binary.Pair Binary.Pair.RandomRun Binary.RandomProvider
set_option maxRecDepth 2048
#eval do
  let (start, config) := recordingState false
  let a := Layout.sequenceAddress - 4
  let memory := put (put start.data.dmem (0xa00000 + Layout.objectSteer) 8 a) a 12 0
  let state := {start with data := {start.data with dmem := memory}}
  let blocks := config.blocks.filter (fun (p : Nat × Nat) => p.1 != Layout.sequenceAddress)
  let config := {config with blocks := blocks ++ [(a,12)]}
  IO.println s!"entry={repr (readyCheck config (context true) state)}"
  match execute 0 20000 state (.ofNat stopAddr) with
  | .error error => IO.println s!"execution={error}"
  | .ok after =>
    IO.println s!"value={after.state.data.regs.rax.toNat}, instructions={after.pcs.size}"
    IO.println s!"count={repr (readNat after.state a 4)}, head={repr (readNat after.state (a+4) 4)}"
    IO.println s!"post={repr (physicalPost config (context true) state after (.ofNat stopAddr))}"
LEAN
```

Observed result:

```text
entry=Except.ok ()
value=7, instructions=462
count=Except.ok 0, head=Except.ok 1
post=Except.error "random.private.steering-counts"
```

Required disposition: repair the physical domain using justified private
resource geometry and retain this case as a cheap rejection regression.
Re-establish the executable-to-propositional readiness bridge, callers and
witnesses, and rerun the actual-body checks. Do not remove a mirror observation
or weaken the failed provider postcondition simply to accept this state.

## R2 — Medium: insertion replay ignores the capture's image and dependency identities

Locations at the reviewed commit:

- `binary/capture_index_mutator.py:207–212` records `kernel`, `image_sha256`
  and `kraken` in each snapshot.
- `binary/PairCapture.lean:85–94` does not retain those fields in `Snapshot`.
- `binary/PairInsertCaptureMain.lean:7–14` decodes the JSON and directly calls
  the runner, without checking these fields separately.
- `binary/PairInsertCapture.lean:53–58` checks anchor, execution mode and
  workload provenance, but no image/dependency identity.
- `binary/README.md:538–543` documents direct replay through that entry point.

Missing or deliberately incorrect values of all three identity fields are
accepted by the snapshot decoder; I confirmed both cases through Lean's
`fromJson?`. The fields are discarded before `run`, so changing only them in
an otherwise passing snapshot cannot affect the replay result. This differs
from the existing lookup driver, which checks the captured image and current
Kraken pin at `binary/pair_capture.py:79–81`.

The capture producer does validate the image and current dependency when it
creates a fresh snapshot. Thus this finding does **not** show that the
reported fresh capture used the wrong image. It means the documented replay
command can silently reuse a snapshot whose identity no longer matches its
proof or executable, defeating a cheap guard against stale or mixed inputs.

Required disposition: check capture identities against the replay's declared
pins before execution and ensure the documented driver checks the actual
current image/dependency. A small control changing each identity should reject
before the expensive memory load and replay; no elaborate audit machinery is
needed.

## What the proof and tests establish

`Insert.insert_checked` proves accepted-return adequacy from the executable
`callBoundary` and `providerCheck`, assuming the named decoder, callback,
physical random-return and recorded-input contracts. The source presentation
is connected to the actual `WG.indexInsert` by checked equalities. Its retry
induction is over the accepted source draw protocol rather than an unrelated
binary budget. `draw_attempt` and `search` derive the locked walk's result from
the retained chain; I found no assumption that simply supplies the desired
second-walk result.

The physical random-return contract and `RandomInputCoupling` are separated
properly in the headline. The latter constrains actual service histories
under a supplied private-state interpretation; it does not demand every
possible draw from a single fixed state or hide a future insertion execution.
It remains unproved and has no concrete proved `inputAt` instantiation in the
positive execution witnesses. Those witnesses prove the two `Pre` instances
and source success; their formal execution conclusions remain conditional on
the service and coupling hypotheses. The runnable witness tests execute those
same concrete states through the actual body. These are distinct forms of
evidence, and neither establishes consistency of every universal service
contract over every admitted configuration.

`InsertSequence.sequence_checked` retains one heap and `Names` interpretation.
`prepare` installs registers and the caller return word; it does not recreate
the WireGuard heap or private provider state. `call_checked` derives later
preconditions from retained `Ready`, static initial facts and source-only
`Admissible` conditions. `SourceBoundaries` and the matched per-call `Boundary`
export intermediate reconstruction and the remaining input. I found no
future-Pre or future-success premise in this composition.

The permission restriction to `EntryDomain` is a real improvement over an
unrestricted prepared-heap quantifier. `ReturningCallPermissions` still
quantifies over any history ending at the stated ABI boundary, including one
that crossed that boundary earlier. The insertion report acknowledges this;
it is not first-return permission safety. The older comment at
`TrustBase.lean:131` about omitting the caller continuation should be read with
that limitation. No new proof of physical permissions or interrupt behavior
is supplied by adding the audit to a history.

The old PC/CMP callbacks in `ServiceImage` are leaf or tail-jump paths; the
no-work BH path is also a leaf. Inspection did not support a separate claim
that their stated endpoints necessarily omit stack stores. Their universal
contracts are still assumptions, not discharged by this observation.

The measurements are explicitly conditioned on the sequential domain, reused
foundation and assumed services. The reported quotient of anchored instructions
per elapsed hour is a descriptive checkpoint measurement, not established
campaign throughput. The 489-instruction cumulative figure is conditional
function-extent accounting, not proof of the random service. R1 requires the
completion narrative to distinguish the existing conditional proof artifacts
from an image-applicable resource specification that is still defective.

## Validation and review limits

I independently ran these commands under `capped`:

- From `binary/`: `lake build PairInsertionSurface binary-pair-random-body
  binary-pair-insert-witness binary-pair-insert-sequence` — passed, 736 jobs.
  Headline/witness axiom reports contain only the three standard axioms.
- From `binary/`: `lake env leanchecker --fresh PairInsertionSurface` — passed,
  exit zero at 23:28:55 UTC, before the coordinator began rebuilding repairs.
- `binary/.lake/build/bin/binary-pair-random-body` — passed the published
  cached, refill, direct/remote recording and saturation cases and controls.
- `binary/.lake/build/bin/binary-pair-insert-witness
  .tmp/binary-insert/input.json` — passed all four runs, 409/434 instructions.
- `binary/.lake/build/bin/binary-pair-insert-sequence
  .tmp/binary-insert-sequence/input.json` — passed all 32 generated sequences
  and their controls. The stored report independently records 416 calls and
  434,064 instructions, agreeing with the reported checkpoint counts.
- The R1 decoded-body counterexample and the R2 JSON-decoding controls above.

The build replay emits inherited module-system/deprecation/reducibility
warnings; it is not a warning-free result. No new warning was found in the
changed modules' build logs. An initial draft of the nonoverlapping-span
counterexample had a Lean type-inference error; the corrected command above
was then executed successfully. No source fix was made by the reviewer.

This was a bounded checkpoint review, not an exhaustive audit of every
instruction lemma or Kraken semantics. I did not rerun the full kernel
differential suite or the roughly ten-minute native capture replay, and did
not run the external export gate. Its acceptance remains pending. The
review is sufficient to identify the concrete checkpoint blockers and assess
the headline/composition structure; it does not certify the remaining
unproved service specifications. The exact review findings and reproductions
are retained here; no trace dump or separate evidence bundle was created.

## Independent follow-up on the repairs

Reviewed the working-tree repairs after `b22264a4` on 2026-10-18, completing
the focused follow-up at approximately 23:38 UTC. The findings above describe
the original checkpoint and remain unchanged. This follow-up inspected the
concrete implementation, its relationship to the fetched body's accesses,
the regression cases, identity handling and updated trust-surface output.

**Verdict: R1 and R2 are addressed by the reviewed repairs. No additional
finding arose in this bounded follow-up.** This assessment closes the concrete
defects above; it does not establish the remaining universal service or input
coupling hypotheses.

For R1, `binary/RandomState.lean:65–82` separates mutable entropy, sequence,
dropped-record and selected steering regions from one another and from the
stable pointer fields actually used by the selected path.
`binary/RandomState.lean:86–127` accumulates those fields while following the
direct or remote graph, including failed bucket matches and the selected
bucket pointer. The checks constrain interpreted roles rather than allocation
cover blocks, so consistent overlapping covers remain admissible. The
postcondition and the mirror observations have not been weakened. The
regression at `binary/PairRandomRun.lean:236` rejects both cover presentations
of the original alias, still executes the bad state to reproduce its failed
postcondition, and checks acceptance of a consistent overlapping cover.

I independently reran the R1 stdin recipe above against the rebuilt repair.
Readiness now returns `Except.error "random.private.role-alias"`. Forced
execution of that rejected state still produces
`Except.error "random.private.steering-counts"` at the physical postcondition.
A separate positive control adding `(0xb00000,192)` to the unchanged
`recordingState false` cover returns `Except.ok ()` from `readyCheck`.
These results support the intended domain repair without hiding the original
behavior or banning benign cover overlap.

For R2, `binary/PairInsertCapture.lean:15–26` makes all three identity fields
mandatory; `:38–42` compares them to the compiled full kernel identity, ELF
hash and Kraken commit. `:72` invokes that check before memory loading or
replay. The documented host driver at `binary/pair_insert_capture.py:33–42`
also checks the current clean dependency, verifies the current kernel,
hashes its ELF and compares the snapshot before invoking Lean. Expanding
`TrustBase.kernelIdentity` to the already recorded full identity makes the
Lean check comparable to the producer's identity value.

Independent focused validation on the repaired tree:

- `capped python3 -B -m unittest binary.test_insert_capture` passed, including
  valid identity and missing/wrong identity subcases.
- `capped lake env lean --stdin` with `import PairInsertCapture` passed the
  original-alias and overlapping-cover controls described above. Direct
  calls to `InsertCapture.checkIdentity` accepted the valid pins and rejected
  unchecked or wrong kernel identity, wrong ELF hash and wrong Kraken pin
  with their corresponding identity errors.
- The same successful stdin run constructed a complete minimal
  `InsertCapture.Snapshot` JSON value and confirmed that it parsed, then
  independently removed `kernel`, `image_sha256` and `kraken`; each missing
  field caused parsing to fail. A draft of this control initially had a
  lambda type-inference error; the explicitly typed correction ran with
  exit zero.
- `git diff --check` passed before this documentation append.

The coordinator separately reported the final default build (793 jobs),
executable build (501 jobs), provider suite with both alias controls, four
exact witnesses, all 32 retained sequences (416 calls, 434,064 instructions),
and binary proof gate passing. Those are coordinator-reported checks, not
additional independent runs by this reviewer. The final fresh kernel replay
and identity-verified native capture were still running when this follow-up
was completed; the external export gate remains separately pending.

This was a focused review of the fixes within the requested ten-minute
budget, not an exhaustive certification of the enlarged physical domain.
`RandomReturnContract`, `RandomInputCoupling` and the other named environment
contracts remain unproved hypotheses. Runtime regressions and a passing
conditional theorem do not discharge them. No implementation was edited by
the reviewer, and no new blocker was identified beyond completing and
reporting the already required final validation.
