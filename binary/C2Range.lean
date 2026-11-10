import C2CutAssembly
import C2RangeTail
import C2RangeAdvance
import C2RangeHead

/-! Work package 2 of result C2: the five segments of the range (`HeadSegment`,
`AdvanceEnters`, `LoopIteration`, `AdvanceStores`, `TailSegment` of `C2CutInterfaces`),
each from the propositions of work package 1 as hypotheses. Brief:
packets/c2/proof/WP2.md.

The proofs are in the modules named `C2Range*`, each registered as a root of
`BinaryProofs`: `C2RangeHistory` (a history-keeping `region_eventually`),
`C2RangeRegions` (the symbolic execution of the ordinary instructions),
`C2RangeSteps` (moving between cut points; the carried invariant under the range's own
stores), `C2RangeHead`, `C2RangeAdvance`, `C2RangeTail` (the segments). -/
namespace Binary.C2

/-- The five segments, from work package 1's propositions as hypotheses. -/
theorem execution (laid : RegionsLaidOut) (pcSite : PcSite) (cmp8Site : Cmp8Site)
    (constSite : ConstCmp8Site) : Execution :=
  ⟨head_segment laid pcSite cmp8Site constSite, advance_enters laid pcSite cmp8Site,
    loop_iteration laid pcSite cmp8Site, advance_stores laid pcSite, tail_segment laid pcSite⟩

/-- The acceptance check of the package: the assembly's `range_simulates` applies to the
five segment theorems. -/
theorem range_simulates_of_sites (laid : RegionsLaidOut) (pcSite : PcSite) (cmp8Site : Cmp8Site)
    (constSite : ConstCmp8Site) : RangeSimulates :=
  range_simulates (execution laid pcSite cmp8Site constSite)

#print axioms head_segment
#print axioms advance_enters
#print axioms loop_iteration
#print axioms advance_stores
#print axioms tail_segment
#print axioms range_simulates_of_sites
end Binary.C2
