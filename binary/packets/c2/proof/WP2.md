# C2 work package 2: the range

Read first: `PLAN.md` here, `AGENTS.md`, `binary/C2Cut.lean` (the pivot `validate`,
the invariant `Carried`, the cut predicates), `binary/C2CutInterfaces.lean`,
`binary/C2Image.lean`.

## Files

You own `binary/C2Range.lean` and new files named `C2Range*.lean`, imported from that
root. Do not edit `binary/lakefile.toml`, the `C2Cut*.lean` files, the statement files
or any landed file.

## What to prove

In `Binary.C2`, each as a theorem whose only hypotheses are WP1's propositions
(`RegionsLaidOut`, `PcSite`, `Cmp8Site`, `ConstCmp8Site`):

| Proposition | Instructions | Call sites | Paths |
| --- | --- | --- | --- |
| `HeadSegment` | +0 to +161 | 1 to 7 | the load and the preempt add; the counter-limit and packet-limit rejections; the too-old rejection; the in-window branch to +280; fall-through to +161 |
| `AdvanceEnters` | +161 to +219 or +263 | 8, 9 | the iteration count and its cap at 128; the loop skipped when the word indices are equal |
| `LoopIteration` | +219 to +219 or +263 | 10, 11 | one word cleared; round again or out |
| `AdvanceStores` | +263 to +280 | 12 | the counter stored |
| `TailSegment` | +280 to +324 | 13 | the `bts`, `%esi`, `setb`; the exit |

`C2CutAssembly.range_simulates` already composes these (the loop's termination
included) into the range against the pivot.

## Where to start

- Regions and straight-line execution: `region_eventually` with a layout from
  `RegionsLaidOut` (through `Reading.range`). It gives `instructionStep` executions
  with no history; the cut predicates need `Quiet` (no state so far at an exit), so
  first prove a history-keeping `region_eventually`: under `LaidOut fetch pc code`
  the states added to the history are at instruction addresses of `code`, which are
  not exits. This is one induction on `LaidOut`, generic, in your prefix.
- Calls: one application of `PcSite`/`Cmp8Site`/`ConstCmp8Site` per site. It returns
  `Carried`, `%rbp`, `%r14`, `%r15` and the two spill slots; nothing else survives a
  call, and the image recomputes every comparison after its callback.
- Trial T3 (`binary-trials/t3` on `task/binary-trials`, unreviewed): `RxRegions.lean`
  has the per-region symbolic executions for the same instructions up to the `bts`
  (30 regions, one instruction per region where the kernel recursed too deep),
  `RxArith.lean` the index arithmetic (`and $0x7f`, `shr $6`, `lea` scaling),
  `RxMemory.lean` the frame lemmas, `RxProof.lean` the composition and the loop
  induction. Take the lemmas, not the statement: T3's invariant had an abstract `K`
  and no history, and it stopped before the `bts`.
- The `bts`: Kraken patch ten, `.deps/kraken/Kraken/X64/Semantics.lean` (`| .bts`);
  the offset is below 64 because of `and $0x3f,%r15d`; CF is the old bit and `setb`
  reads it; the other five flags are undefined and nothing reads them.
- `Carried.coverage` under your own stores: `Kcov.state_frame` with
  `Context.coverageApart`, `stackPreempt`, `windowPreempt`; the add to the preempt
  count changes the count the invariant names (`preempt` to `preempt + 0x200`).

## Dependencies

WP1's four propositions, as hypotheses only. Nothing from WP3.

## Estimate, risk, acceptance

- 7 to 11 worker-hours: history-keeping regions 1, head 2 to 4, advance and loop 2 to
  3, tail with `bts` 1 to 2, slack 1.
- Main risk: the cut predicates were written before these proofs. If one is too weak
  to continue from (a register or slot fact missing at a cut) or false at its
  address, that is a finding against the cut: report it with the instruction, do not
  patch around it in a segment.
- Acceptance: build and `scripts/binary-proof-gate` pass; `#print axioms` on the five
  theorems shows the standard three; `Binary.C2.range_simulates` applied to them
  type-checks in your root file; no file outside your prefix changed; resource-limit
  raises scoped and listed.
