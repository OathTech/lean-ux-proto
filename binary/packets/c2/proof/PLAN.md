# C2 proof plan: the cut into work packages

The signed statement is `binary/C2Statement.lean`
(`HeadlineRefinement := ExitsCleanly ∧ Refines ∧ NoCounterAcceptedTwice ∧ ReplayWitness`).
This plan cuts its proof into three packages with interfaces fixed in Lean. Nothing
in the statement files is changed, and nothing is proved about the image yet: the
assembly theorems are conditional on the packages' propositions.

Since this plan was written the three packages closed and the integration pass joined
them: see `docs/2026-11-10-c2-replay-window.md`. The plan is kept as written.

## What is fixed in Lean

| File | Holds | Who edits |
| --- | --- | --- |
| `binary/C2Cut.lean` | the pivot (`Window`, `WindowAt`, `validate`), the carried invariant (`Carried`), the cut predicates (`AtAdvance`, `AtLoop`, `AtStore`, `AtTail`, `AtExit`) | nobody |
| `binary/C2CutInterfaces.lean` | 22 interface propositions | nobody |
| `binary/C2CutAssembly.lean` | `range_simulates`, `refines_of_parts`, `exits_cleanly_of_parts`, `replay_witness_of_parts`, `headline_of_parts`, proved from the propositions | the integration pass |
| `binary/CallbackCmp8Image.lean`, `binary/CallbackCmp8Rule.lean` | the two 8-byte entries and the three callback rules, stated once for C1 and C2 | nobody |
| `binary/bridge/C2Bridge.lean.proposed` | `no_counter_accepted_twice`, `headline`, from `Refines` and the proof tree's `CounterWindow` (see `BRIDGE.md`) | the integration pass |
| `binary/CallbackCmp8.lean`, `binary/C2Callbacks.lean` | roots of WP1 | WP1 |
| `binary/C2Range.lean` | root of WP2 | WP2 |
| `binary/C2Sequences.lean` | root of WP3 | WP3 |

All are roots of `BinaryProofs` already. A prover adds files under its own prefix and
imports them from its root; nobody edits `binary/lakefile.toml`.

## The pivot and the carried invariant

The packages meet at one function, `validate : Window → BitVec 64 → Outcome`: the
range at machine width (unsigned comparisons and wrapping sums on the values the
instructions use). WP2 proves the machine computes it; WP3 proves the mirror's
`counterValidate` computes it. It is executed against the mirror on 2,925 boundary
cases by `binary/packets/c2/proof/check` (`C2CutTest`).

The cut predicates are executed too (`C2CutTrace`, same script): the range and the
callbacks' image code are run under Kraken from the constructed entry states of the
statement's tests, with coverage off, in PC mode and in comparison mode, and at every
arrival at a cut address the decidable content of its predicate is compared with the
machine state; across every call the content of `CallSite`'s conclusion is compared.
512 runs, 41,760 calls and 18,544 loop iterations held. Three one-off mutants of the
test (a wrong `%rbp` in the loop invariant, a wrong value for a spill slot, a
caller-saved register claimed kept across a call) each failed it; they were run once
and deleted. This is evidence that the propositions are true on those runs, not a
proof, and it does not exercise the frame, the coverage state or `Quiet`.

`Carried layout preempt kp s0 w d` holds at every point from +14 on, across each of
the thirteen calls and at the head of each loop iteration:

- coverage readiness: `KcovState layout (preempt + 0x200)`;
- the window bytes hold the window in progress `w`;
- the three stack slots (return address, `0x10(%rsp)`, `0x18(%rsp)`) are mapped;
- memory equals the entry's outside the footprint and the coverage buffer;
- `%rsp`, `%rbx`, `%r12`, `%r13` are the entry's.

Path state is in the cut predicates: the spill slots' values, `%rbp`, `%r14`, `%r15`
(the only registers live across a call), and `Quiet` (no state so far at an exit). The
loop invariant is `AtLoop … i`: `i` words cleared, `%r14` the stored counter's word
index, `%rbp = i + 1`, `%r15` the iteration count, `i` below it.

## Dependency graph

```
WP1  rules (PcRule, Cmp8Rule, ConstCmp8Rule) ──> call sites (PcSite, Cmp8Site, ConstCmp8Site)
     BtsSupported ──> RegionsLaidOut                    │
                           │                            │
                           └────────────┬───────────────┘
                                        v   (as hypotheses)
WP2  HeadSegment, AdvanceEnters, LoopIteration, AdvanceStores, TailSegment
                                        │
                                        v   C2CutAssembly.range_simulates   (proved)
                                 RangeSimulates
                                        │
WP3  representation, mirror link ───────┤   refines_of_parts, exits_cleanly_of_parts (proved)
     first exits, WitnessStart ─────────┤   replay_witness_of_parts                  (proved)
                                        v
                 ExitsCleanly ∧ Refines ∧ ReplayWitness
                                        │   bridge: no_counter_accepted_twice        (proved)
                                        v
                                HeadlineRefinement
```

The three packages start together. WP2 takes WP1's propositions as hypotheses; WP3
depends on nobody. No package waits for another.

## Packages

| | Proves | Worker-hours | Main risk |
| --- | --- | ---: | --- |
| WP1 | 3 rules, `StubsAgree`, `BtsSupported`, `RegionsLaidOut`, 3 call sites | 7 to 12 | coverage readiness for the constant 8-byte callback, which has no `KcovKind` |
| WP2 | the 5 segments | 7 to 11 | a cut predicate too weak or false at its address |
| WP3 | 11 propositions | 6 to 10 | a recording-mode witness; the mirror's monad plumbing |
| Integration | closed theorems, gates, surface | 2 to 3 | below |

20 to 33 worker-hours of proof, 22 to 36 with integration; the statement packet
planned 25 to 30. Briefs: `WP1.md`, `WP2.md`, `WP3.md`.

## Integration order

1. WP1's neutral half lands first on this branch (`CallbackCmp8*`), because C1 needs
   it: the C1 branch takes `CallbackCmp8Image.lean`, `CallbackCmp8Rule.lean` and
   `CallbackCmp8*.lean` unchanged, and proves on its side that its own image terms
   (`StatementC1CallbackImage.fetch`) give `Callback.Cmp8.Cmp8Agreement` (its image has the
   variable form only, so each 8-byte rule asks for its own entry alone). This branch
   owns those modules; C1 does not edit them.
2. WP1's C2 half, WP2, WP3, in any order: they touch disjoint files.
3. The integration pass.

## Left for the integration pass

- Closed theorems: instantiate WP2's segment theorems with WP1's, build `Execution`
  and `Representation`, and state `Binary.C2.exits_cleanly : ExitsCleanly`,
  `refines : Refines`, `replay_witness : ReplayWitness` in the package and
  `Binary.C2.Bridge.headline_refinement : HeadlineRefinement` in the bridge.
- `binary/surface.py`: add the headline and witness to `HEADLINES`/`IMPORTS` and
  regenerate `TrustSurface.expected.txt` (a reviewed baseline change).
- The bridge proposal to the owner (`BRIDGE.md`): the three diffs, the rename, the
  named gate, the register row.
- `binary/README.md` results table and `docs/proofs.md`; the kernel replay export
  list (`C2Statement`, the closed theorems' modules).
- The optional clause `AcceptedWithinWindow` and the two exclusions (`ReplayRefused`,
  `AdvanceAccepted`) are in no headline and in no package. `ReplayRefused` follows
  from the bridge in a few lines; the floor needs `step_accepted_bounds`,
  `step_counter_mono` and `accepted_remembered`. Decide at integration whether to do
  them.
- Independent review of the whole.

## Risks, ranked

1. **Coverage readiness for the constant 8-byte callback (WP1).** The landed
   `KcovInvariant` lemmas are indexed by `KcovKind`, which has no constructor for
   tag 7, and `TrustBase.lean` is not to be edited for this. The rule is stated by a
   tag-indexed plan (`recordPlan`); re-establishing `KcovState` after its stores needs
   tag-7 counterparts of about five landed lemmas. This is the statement packet's
   named main uncertainty, now confined to one package.
2. **The call-site rule and the cut predicates are unproved.** The assembly proves
   they suffice for the headline, and the executed trace above found their register,
   slot and window content true on 512 runs. Nothing yet proves them, and nothing
   tests whether WP2 can continue from `CallSite` and the cut predicates as stated
   (a fact needed across a cut may be missing). T3 used a rule of the same shape with
   an abstract invariant. A package that finds one false or too weak reports it; the
   fix is to the cut, by the coordinator, and the assembly is rechecked.
3. **`Context`'s separations hold only in a recording mode.** The landed
   `Kcov.callback` wants them unconditionally. A case split on the mode with
   `Kcov.inactive_plan` should do; it was not tried.
4. **History.** The statement is in first-exit form over recorded histories; the
   landed `region_eventually` forgets the history. WP2 needs a history-keeping variant
   (one induction) before any segment.
5. **The witness in a recording mode (WP3)**: a concrete memory meeting every
   separation with a real coverage buffer.
6. **The bridge rule change is not approved.** Until it is, the transported clause and
   the headline theorem exist only in a staged file outside every gate except
   `binary/bridge/check`. If the owner declines, the fallback of the statement packet
   (copying about 250 lines of `CounterWindow/Model.lean` into the package) costs 2 to
   3 hours and changes what the clause may be called.
7. **Kernel depth.** T3 hit kernel deep recursion on a three-instruction region;
   regions may have to be one instruction each.

## Checks

```sh
cap() { if command -v capped >/dev/null 2>&1; then capped "$@"; else "$@"; fi; }
cap scripts/in-bundle lake -d binary build
scripts/in-bundle "$(command -v python3)" scripts/binary-proof-gate
binary/packets/c2/check            # the statement's executed tests
binary/packets/c2/proof/check      # the pivot against the mirror; the cut predicates against Kraken (4 minutes)
binary/bridge/check                # the staged bridge: compile, axioms, tokens, imports
```
