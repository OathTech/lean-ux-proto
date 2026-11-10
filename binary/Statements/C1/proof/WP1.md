# C1 work package 1: the source side and the invariant's algebra

Prefix `binary/C1Source*.lean`, root `binary/C1Source.lean`. Read `PLAN.md`
(sections 1 to 3) first; its rules apply.

## To prove (acceptance theorems, in `Binary.Statements.C1.Proof`)

| Theorem | Type (`C1Interfaces`) |
| --- | --- |
| `runIsStep` | `RunIsStep` |
| `initialHolds` | `InitialHolds` |
| `framedHolds` | `FramedHolds` |
| `lookupHolds` | `LookupHolds` |
| `exclusionOne` | `ExclusionOne` |
| `exclusionTwo` | `ExclusionTwo` |

`RunIsStep` is the bulk. For an accepted
`(liftWG (WG.insert family key cidr pid)).run w = .ok (answer, w')` under
`Inv` and `insertReady` it must produce `StepFacts`: the mirror's device and
records; `ordered d` (from `Inv`); the family and the key bound (from
`insertReady`: `c1.family`, `Trie.networkKeyCheck`); the run as
`C1Step.step` up to `Allowedips.target`, with the answer, the records
consumed, their sites and outcome bytes; `armed w'`; and, where the walk is
reached, `nodePlacement`'s own accepted run in the form
`Placement.loop_checked` takes together with `C1Invariant.walk`.

## Start from

- Landed, in `binary/`: `assertAt_ok`, `assertAt_of_related`, `heap_checks`,
  `Trie.heap` and `Trie.decodeNode` (for `ordered`); `AllowedipsSourceModel`,
  `AllowedipsSourceRun`, `SourceAip`, `SourceAllowedips`,
  `PairAllowedipsPlacementSource`, `AllowedipsPlacementSourceStep`,
  `AllowedipsExactSource`, `AllowedipsChildSource`, `AllowedipsRootTree` (run
  equations and endpoint formulas for the root, exact and child cases);
  `PairAllowedipsReadSet`, `PairAllowedipsHeapFrame`, `PairAllowedipsFrame`,
  `PairAllowedipsLookupFrame` (reads of the relation, for `Framed`);
  `lookup_checked` and `lookupBoundary` in `PairAllowedipsLookupAdequacy` /
  `PairAllowedipsLookupCheck` (for `LookupHolds`); `TrieHeap` (`common`,
  `fls` arithmetic).
- Trials (branch `task/binary-trials`, lemma sources only, unreviewed):
  `t2/CoverSource.lean`, `t4/T4Source.lean`, `t5/T5RootSource.lean`,
  `t5/T5Bridge.lean`. They link endpoint formulas to connection steps run from
  hand-built devices, not to `Leanux.WG.add`; that link is this package's work.
- Not importable: `Leanux/Proofs/WG/AllowedIps/` (`PlacementMirror`,
  `GraftMirror`, `DeepGraft`, `InsertionDispatch`). Read them for the shape of
  the argument; re-prove locally.
- Tests: `C1Step.stepCheck` and `C1Invariant.walkCheck` already pass on every
  insertion of the packet's test and the capture; a failing sub-lemma can be
  evaluated the same way.

## Depends on

Nothing from other packages. `ExclusionOne` / `ExclusionTwo` take
`HeadlineFor` as their hypothesis.

## Notes on each

- `ordered` from `Inv`: unfold `Related`, `assertAt_ok`, `heap_checks`; the
  edge clauses are `Trie.heap`'s three checks transported through `target`;
  the node clauses are `Trie.decodeNode`'s (`node.prefix`, the key widths).
- The walk facts: an induction over `nodePlacement`'s bounded loop. Invariant
  of the loop: the current node is of the family's width and, if there is a
  placed node, the key shares its prefix, its prefix is shorter than `cidr`
  and the current node is its child on the key's side. The table in `PLAN.md`
  section 1 says which fact each exit gives.
- `InitialHolds`: the interpretation is `⟨L.table, ⟨[], L.peers⟩, d.nextNode⟩`.
- `FramedHolds`: needs `Premises` only for the contract's `frame` clause.
- `LookupHolds`: `Premises` names the callbacks `lookup_checked` takes, except
  that `AllowedipsTraceConstCmp1Contract` comes from `callbacks.constCmp1`.
  Its conclusion's `Trie.CountBytes` must be shown inside `L.Heap`, and
  `AllowedipsTail.Post` to give `Returned` and `rax`. The mirror's lookup must
  be shown to leave the pending records and the armed sites alone.
- Exclusions: `Initial` at the empty table, `InsertStep` with the run
  `MirrorAccepts` supplies, `Framed` across `HeapSame`, `LookupStep` with the
  lookup `MirrorAccepts` supplies; the mirror facts are that `step` at an empty
  root is `root` with answer 0 (outcome 1) or `rootNoMem` with `-ENOMEM`
  (outcome 0), and that the lookup then finds `pid` or nothing. `peer ≠ 0` is
  `insertReady`'s `c1.insert-peer`.

## Estimate and risk

14 to 20 worker-hours. Main risk: the loop induction with its recorded
decisions (`branch`, `branchCmp` write the ambient state at every step), and
nine run equations of which three exist in the package. If a run of the
mirror is accepted on a state where `step` differs, that is a finding about
`C1Step` (report it), not something to patch in `StepFacts`.

## Acceptance

The six theorems with exactly those types; `#print axioms` on each;
`lake -d binary build` and `scripts/binary-proof-gate` pass.
