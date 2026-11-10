import C1BelowCover
import C1BelowWhole
import C1BelowUndoFinal

/-! Result C1, work package 3: what is proved, and what is not.

NOT PROVED: the interface propositions `PathCover`, `PathSplit` and
`PathSplitNoMem` of `C1Interfaces`. They take `TrunkToNode`, whose `NodeCut`
does not determine the machine's behaviour from `add+0x156`: four facts
about the cut state are missing (`CutExtra` in `C1Cut`, each with
the instruction that consumes it).

PROVED: the same three propositions with `TrunkToNodePlus` (`TrunkToNode`
with `CutExtra` beside `NodeCut`, `C1Cut`) in place of `TrunkToNode`,
and nothing else changed. `paths_below` collects them. -/
namespace Binary.Statements.C1.Proof

/-- The three paths below the placement, from the strengthened trunk. -/
theorem paths_below :
    (TrunkToNodePlus → Path .cover) ∧
    (NodeBelowTop → AllocRule → TrunkToNodePlus → Path .split) ∧
    (AllocRule → FreeRule → TrunkToNodePlus → Path .splitNoMem) :=
  ⟨pathCover_plus,pathSplit_plus,pathSplitNoMem_plus⟩

#print axioms pathCover_plus
#print axioms pathSplit_plus
#print axioms pathSplitNoMem_plus
#print axioms paths_below
end Binary.Statements.C1.Proof
