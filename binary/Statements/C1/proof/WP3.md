# C1 work package 3: the paths below the placement

Prefix `binary/C1Below*.lean`, root `binary/C1Below.lean`. Read `PLAN.md`
(sections 1 to 3) first; its rules apply.

## To prove (acceptance theorems, in `Binary.Statements.C1.Proof`)

| Theorem | Type (`C1Interfaces`) | Path from `add+0x156` |
| --- | --- | --- |
| `pathCover` | `PathCover` | initialization, selection, `common_bits`, the new node covers the node below: connections at the root and below a parent, common exit |
| `pathSplit` | `PathSplit` | the same to the comparison, second allocation, the internal node's initialization, three connections at the root and below a parent, common exit |
| `pathSplitNoMem` | `PathSplitNoMem` | the same to the second allocation, NULL: `list_del`, the release, `-ENOMEM`, common exit |

Each is a whole `Path k` (wrapper entry to the caller's return): compose
`TrunkToNode` (hypothesis) with this package's segment from the cut to
`add+0x549` and the cut's `Exits`.

## Start from

- Landed: `NodeInit.initialization_core_checked` (`AllowedipsNodeCore`,
  `add+0x156` to `+0x1ff`), `NodeInit.BoundaryFields`, `NodeInit.Pending`
  (`AllowedipsNodeBoundaryFields`, `AllowedipsNodePending`), the selection
  modules (`AllowedipsSelect*`), `common_checked` at `add+0x255`, the child
  case's data lemmas (`AllowedipsChild*`, `AllowedipsConnect*`,
  `AllowedipsTrieChild*`, `AllowedipsTrieEdge*`) as the pattern for a
  connection store restoring reconstruction and `heap`; the peer-list ring
  lemmas (`AllowedipsRing*`, `AllowedipsPeerList*`) for the rollback's
  `list_del`.
- Trials (`task/binary-trials`, unreviewed, lemma sources only): T1 (22
  instructions of the covering path, `t1/Direct.lean`); T2 (`CoverReconstruct`,
  `CoverHeap`, `CoverIncoming`, `CoverTrieHeap`: the covering node's data side
  below a parent, as memory terms); T5 (`T5Machine`, `T5Path`, `T5Heap`,
  `T5Reconstruct`, `T5Return` and the `Root` variants: the intermediate node's
  three connections and tail).
- What the trials left in hypotheses, which this package must derive and not
  assume again (the reassessment's review, M1): T2's eight path facts and T5's
  ordering and side facts are now `StepFacts.walked` (`C1Invariant.walk`) and
  `StepFacts.trie` (`ordered`); T2's root sub-case is untreated; T5's
  `InternalInit` (the 45 instructions initializing the internal node) was
  declined, not reached; T5's link between the machine's selected bits and
  the mirror's `choose`; the mirror link is to `C1Step.step`'s device through
  `StepFacts.after`, not to a hand-built device. The rollback has no trial.

## Depends on

- `TrunkToNode` (package 2): the cut `NodeCut` at `add+0x156`.
- `AllocRule`, `FreeRule` (package 4): the second allocation and the release.
  After a service call the rule gives `Protected` bytes unchanged and
  `InFlight`; the stores made since the last call fall in kept nodes or
  outside the arena, so `Idle` is carried by the contract's `frame` clause
  (from `Premises`).
- `StepFacts` (package 1). `NodeBelowTop` (open) for the second node.

**First task (before proving):** `cutCheck` in the packet's test evaluates
the cut's decidable part on every insertion. List what the three paths need
at `add+0x156` that `NodeCut` does not give (a register, a stack word, a
separation: compare T5's 48 hypotheses with `NodeInit.boundary`'s checks) and
report it; the cut is the least-proved interface of the plan. The end of each
path is `Exits`: reach `add+0x549` with the cut's stack pointer, the words
from `rsp+48` up intact, `InFlight`, `CallsReady` and `Inv` for the mirror's
final world, and `Exits` gives `Returned`, `eax`, the heap unchanged and `Inv`
at the return; `SeqAdvanced` follows from the cut's and the heap clause.

## Estimate and risk

14 to 22 worker-hours, the largest package and the one most likely to
overrun. Main risk: the internal node's initialization and the rollback are
unlike anything landed or tried; the conclusion needs `Inv` for the mirror's
world, which for `splitNoMem` means the interpretation without the released
node, the mirror's allocation counter advanced, and the peer's list restored
byte for byte. If it overruns, `pathSplit` can go to another worker with no
interface change.

## Acceptance

The three theorems with exactly those types; `#print axioms` on each;
`lake -d binary build` and `scripts/binary-proof-gate` pass.
