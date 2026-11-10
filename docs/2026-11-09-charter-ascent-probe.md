# Charter: the Ascent / Kraken-WP probe on the binary track

Status: experiment closed; see [the closing report](2026-11-10-ascent-probe.md). Nothing here is a
result. No merge to `main` and no push is authorized by this charter.

## Decision and provenance

- **[USER 2026-11-09]** Run the bounded experiment recommended by the
  assessment of `sgraf812/ascent` (branch `fork/tracer`) and the Kraken fork
  it depends on (`sgraf812/kraken`, branch `vcgen`): test whether that
  tooling removes the per-instruction and bookkeeping cost of the binary
  refinement proofs. The coordinator orchestrates worker agents. Building the
  external code is approved for this purpose.
- **[AGENT 2026-11-09, coordinator]** Everything below: the client, the
  stages, the budgets, the stop conditions, the layout.

## Question

Our 21 October diagnosis (the unlanded local-contracts proposal, `f4e4ba55`
on `task/binary-heap-view`) was that binary proofs unfold Kraken's
interpreter per instruction, redo address and width arithmetic, and assemble
register and frame facts by hand. The fork's weakest-precondition layer
(instruction specs, `vcgen`, `kfinish`, function specs, call and frame
rules, sound against `Eventually (step1 Host.exe)`) and Ascent's `ascend`
lifting are an existing implementation of the interface that proposal
wanted to build. Does it work on our code, at what porting cost, and does it
make a real segment cheaper to prove?

## Client

Client A of the local-contracts proposal, unchanged:
`Binary.Pair.Allowedips.Placement.ChildInput.segment`
(`binary/AllowedipsPlacementSaved.lean`), from `Add.entry + 0xca` through
the real PC callback, the child selection and the branch, to `+0x55f` or
`+0xf7`. Both address families, symbolic addresses and every alias the
existing `ChildInput` and `Frame` admit stay in the domain. The sibling must
check at the old theorem's exact type, or at a type shown equivalent across
the bridge of stage 1, with the equivalence proved, not asserted.

## Stages

| Stage | Work | Budget (elapsed) | Stop and report if |
| --- | --- | --- | --- |
| 0a | Rebase our nine Kraken patches onto the fork's `vcgen` head; build the fork with them on `nightly-2026-11-07`; keep our semantics tests passing | 3 h | a patch cannot be carried without changing instruction meaning |
| 0b | Build the mirror modules the binary package imports on the nightly | 2 h | the mirror needs a source change beyond a mechanical toolchain fix (the mirror rule: report, do not edit to fit) |
| 0c | Build Ascent and its demo; reproduce its numbers; write the image-bridge design: our `instructionStep fetch` over the s5 image against the fork's `Host` / `Program` model | 3 h | the demo does not build, or no sound bridge exists without a new trusted assumption |
| 1 | Port client A's dependency closure; prove the bridge; re-prove client A with the fork's WP layer only (specs, `vcgen`, call rule for the callback) | 8 h | A does not close; record the obstacle, do not add a second client |
| 2 | Only if stage 1 closes: lift the same segment with `ascend` and connect the lifted program to the existing source step | 6 h | `ascend` needs a call rule or heap rule that is new engine work rather than a rule instance |

Stage 2 does not start without a coordinator checkpoint on stage 1's
measurements. Budgets are caps, not targets. A stage that hits its stop
condition ends with a report; a repair that would fit the remaining time is
proposed, not started.

## Fixed constraints

- The s5 image, the mirror and the statement of client A do not change. A
  mirror discrepancy is a Rule Zero report.
- The Kraken pin does change, inside this branch only: fork `vcgen` head plus
  our rebased patches. That is a trust-surface change of the experiment and
  is reported as one; the landed binary package and its pin are untouched.
- No `sorry`, no non-standard axiom, no `native_decide`, no warning
  suppression. A resource raise is per declaration, with its reason,
  and reported.
- New instruction specs are proved from Kraken's interpreter; none is
  assumed.
- Heavy jobs run through `capped`; each worker stays at or below 24G and
  checks the account total before starting. KILLED or timeout is a failure.

## Layout

- `binary-ascent/`: the experiment's own lake package (its own
  `lean-toolchain`), so the landed `binary/` package keeps building on
  v4.35.0 beside it.
- `binary-ascent/kraken-patches/`: the rebased patch series and the fork
  commit it applies to.
- `.tmp/kraken-vcgen/` (ignored): the private patched fork checkout. The
  shared `.deps/kraken` is not written.
- The nightly toolchain lives in an isolated `ELAN_HOME`
  (`/tmp/ascent-assess-182411/elan` during the run); the machine's shared
  elan home is not modified. A clone elsewhere installs the nightly the
  ordinary way.

## Measures

As in section 5 of the local-contracts proposal, reduced to what one client
supports: porting cost by stage (elapsed, lines, files), new instruction
specs and rules needed, unsuccessful check cycles, the manual obligations
left in the A proof (address and word conversions, frame reconstruction,
call setup) with representative code, proof size against the existing
closure of `ChildInput.segment`, and three warm check times. Historical
proofs are structural baselines, not labour baselines.

## Verdict forms

- **Usable**: A closes through the WP layer with the interpreter not
  unfolded in the client and frame facts handled by shared rules; propose a
  second client and the `ascend` stage.
- **Usable with named engine gaps**: A closes but needs engine or fork work
  listed with its size; put the list to the user (and upstream).
- **Not usable here**: the bridge, the port or A fails; name the obstacle.

Allocation identity, structural heap mutation, entry realism and
concurrency are unmeasured in every verdict.

## Stage 3: a fresh segment, proved both ways

- **[USER 2026-11-10]** After stage 2 reports, run the comparison the
  local-contracts proposal specified and never ran: a heap-mutating segment
  nobody has proved, attempted by the current direct method and through the
  WP layer by separate fresh workers under the same budget. The point is to
  measure authoring and discovery cost, which stage 1 (a known proof
  re-done) did not; slower checking is accepted if authoring is cheaper.
- **[AGENT 2026-11-10, coordinator]** The details below.

Scoping first, by one worker that proves nothing: choose a segment of the
unfinished allowed-IPs insertion path that is not covered by any landed
theorem, runs between two existing cut points, is 10 to 30 instructions,
performs at least one store into a trie node and reads back through it, and
whose pre- and post-conditions can be stated over existing definitions.
Write the target statement, test it against the constructed-state runner or
an executed instance where one exists, extend the ported closure to the
definitions both arms need, and prove any missing instruction specs so that
spec coverage is not charged to the WP arm's clock (their cost is reported
separately as setup). The statement, the allowed dependency boundary and
the base commit are frozen before either arm starts.

Two arms, each a fresh worker in its own worktree from the frozen commit,
same toolchain, same patched Kraken, same model, three hours each, no
cross-reading until both report:

- **Direct**: the landed method (interpreter unfolding by `simp`, region
  lemmas, the closure's frame rules); `binary-ascent/wp` is out of bounds.
- **WP**: the fork's layer through `binary-ascent/wp` (specs, `vcgen`,
  `kfinish`, the bridge); interpreter unfolding in the client is out of
  bounds.

Both may read every existing proof. Neither may change the statement. Each
records prospectively: time to first checked theorem, unsuccessful check
cycles by class, facts that had to be discovered (invariants, frame and
alias conditions, arithmetic), lines, and warm check time. An arm that does
not close in its budget is censored data, reported with its open goals, not
a number. The coordinator checks both statements and that each arm used its
method. One pair has author and ordering noise; the result is an
engineering screen, and a statement found to be false or unprovable as
written is reported as a scoping failure, not repaired inside an arm.

