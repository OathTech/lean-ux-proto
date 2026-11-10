import C2CutAssembly
import C2RangeTail

/-! Work package 2 of result C2: the five segments of the range (`HeadSegment`,
`AdvanceEnters`, `LoopIteration`, `AdvanceStores`, `TailSegment` of `C2CutInterfaces`),
each from the propositions of work package 1 as hypotheses. Brief:
packets/c2/proof/WP2.md.

The proofs are in the modules named `C2Range*`, each registered as a root of
`BinaryProofs`: `C2RangeHistory` (a history-keeping `region_eventually`),
`C2RangeRegions` (the symbolic execution of the ordinary instructions),
`C2RangeSteps` (moving between cut points; the carried invariant under the range's own
stores), `C2RangeHead`, `C2RangeAdvance`, `C2RangeTail` (the segments). -/
