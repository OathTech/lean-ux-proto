# C2 work package 3: representation, the mirror, sequences, the witness

Read first: `PLAN.md` here, `AGENTS.md`, `binary/C2Cut.lean`,
`binary/C2CutInterfaces.lean`, `binary/C2CutAssembly.lean` (how your propositions are
used), `binary/bridge/C2Bridge.lean.proposed` (the other user).

## Files

You own `binary/C2Sequences.lean` and new files named `C2Sequences*.lean`, imported
from that root. Do not edit `binary/lakefile.toml`, the `C2Cut*.lean` files, the
bridge, the statement files or any landed file. Nothing in the binary package imports
`Leanux.Proofs`.

## What to prove

In `Binary.C2`, closed theorems:

| Proposition | Content |
| --- | --- |
| `WindowMapped` | 1032 mapped bytes hold some `Window` |
| `WindowOfFields`, `FieldsOfWindow` | `Layouts.ReplayFields` and `WindowAt` through `ofCounter`/`toCounter` |
| `FieldsFit` | a represented state has a counter and words below 2^64 and 128 words |
| `FieldsRetained`, `FieldsMapped` | the representation reads exactly the window bytes, and they are mapped |
| `MirrorFollowsSpec` | a successful run of the mirror's `counterValidate` returns and leaves what `validate` does, and `exitPC` is its exit |
| `WorldHolds` | every replay state is held by some world; an `Ambient` exists |
| `FirstExitDetermined`, `FirstExitExists` | an `Eventually` proof to a first exit against an actual first exit |
| `WitnessStart` | the concrete witness: decoder, entry state, world, two mirror runs, revisitability |

## Where to start

- Representation: `Mem.loadInt` against `get?` byte by byte; `MemoryBytes.lean`,
  `CanonicalLoads.lean`, `Memory.lean` (`EqualOutside.loadInt`, `loadInt_range`).
  Address forms are the ones `ReplayFields` uses, on purpose.
- The mirror link. `binary/packets/c2/proof/C2CutTest.lean` executes the claim on
  2,925 boundary cases (run `binary/packets/c2/proof/check`). For the proof: T3's
  `RxMirrorRun.lean` (monad plumbing of `WG.M`: `branch`, `branchCmp`, `getKeypair`,
  `setKeypair`, the `forIn`) and `RxMirror.lean` (`clear_eq`, the Nat transcription)
  on `task/binary-trials`, unreviewed. The proof tree's `CounterWindow/Refinement.lean`
  proves the same run equation; you may read it, you may not import it, and copying
  it is the option the owner did not take: prove against `validate` directly.
- First exits. `HistoryGuard.history_witness` gives a leaf of an `Eventually` proof;
  `FiniteExecution.eventually_actual` and `instruction_successors` relate `Eventually`
  to `ActualHistory`. `FirstExitDetermined` is an induction on the actual history
  beside the proof tree: at each state either the proof is done there (then the state
  is at an exit, so it is the history's last) or it steps and the actual successor is
  one of its branches; a proof still stepping at the last state would have a leaf
  whose history holds an exit before its end.
- The witness. `binary/packets/c2/C2Test.lean` builds concrete entry states and checks
  `Context` field by field (`contextHolds`; appendix A3 of
  `docs/2026-11-10-c2-final-statement.md`); `LookupWitness*.lean` are the landed model
  of a theorem witness. The decoder is the range's literal terms or else
  `ServiceImage.fetch`. Revisitability is from `Kept` and the two mapping facts: put
  the packet's counter slot outside the footprint and the coverage buffer.

## Dependencies

None for the propositions. The clause `ReplayWitness` itself is assembled from
`WitnessStart` and WP2's result in `C2CutAssembly.replay_witness_of_parts`; you do not
prove it.

## Estimate, risk, acceptance

- 6 to 10 worker-hours: representation 1 to 2, mirror link 2 to 3, first exits 1 to
  2, witness 2 to 3.
- Main risk: `WitnessStart` in a recording mode needs a concrete memory that
  satisfies every separation of `Context` with a real coverage buffer; a witness with
  coverage off (mode 0) is weaker evidence and must be reported as such if that is
  what you can prove. Second: the mirror link's monad plumbing (six failed cycles in
  T3).
- Acceptance: build and `scripts/binary-proof-gate` pass; `#print axioms` on the
  eleven theorems shows the standard three; a term of `Binary.C2.Representation`
  built from them in your root file; `binary/packets/c2/proof/check` and
  `binary/packets/c2/check` still pass; no file outside your prefix changed.
