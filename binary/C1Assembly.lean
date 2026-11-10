import C1Interfaces

/-! Result C1, proof plan: `Signed` assembled from the interface propositions
of `C1Interfaces`. These theorems are proved now, so the top-level cut is
checked: when the four packages have proved their propositions,
`signed_of_parts` is the result. `NodeBelowTop`, an open hypothesis under
revision 2 of the statement, is derived here from revision 3's `AllocResult`.

What this file does not check: that `TrunkToNode` (the machine cut handed
from package 2 to package 3) and the two service rules give the path
packages enough to prove their paths. Those are hypotheses of the path
propositions, not of anything proved here. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-- The node bound, from `AllocResult`'s success clause (revision 3). -/
theorem nodeBelowTop : NodeBelowTop :=
  fun _ _ _ _ _ _ _ _ result success => (result.2 success).2.2.1

/-- `InsertStep` from the source-side classification and one path per case. -/
theorem insertStep_of_paths (run : RunIsStep) (paths : ∀ k, Path k)
    (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator) (premises : Premises fetch L A) :
    InsertStep fetch L A (Inv L A) := by
  intro c s w w' family key cidr pid ra answer inv ready accepted
  obtain ⟨d,stream,placed,exact,st,facts⟩ :=
    run L A c s w w' family key cidr pid ra answer inv ready accepted
  exact paths st.case fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st
    inv ready accepted facts rfl

/-- Every case has its path, from the nine path propositions, the trunk, the
two service rules, `Framed` for `Inv` and the node bound. -/
theorem paths_of_parts (below : NodeBelowTop) (framed : FramedHolds) (alloc : AllocRule) (free : FreeRule)
    (trunk : TrunkHolds) (tooLong : PathTooLong) (rootNoMem : PathRootNoMem) (root : PathRoot)
    (exact : PathExact) (nodeNoMem : PathNodeNoMem) (child : PathChild) (cover : PathCover)
    (splitNoMem : PathSplitNoMem) (split : PathSplit) : ∀ k, Path k := by
  have cut : TrunkToNode := trunk below framed alloc
  intro k
  cases k
  · exact tooLong framed
  · exact rootNoMem framed alloc
  · exact root below framed alloc
  · exact exact framed
  · exact nodeNoMem framed alloc
  · exact child below framed alloc
  · exact cover cut
  · exact splitNoMem alloc free cut
  · exact split below alloc cut

/-- The four clauses for `Inv`. -/
theorem headlineFor_of_parts (initial : InitialHolds) (framed : FramedHolds) (run : RunIsStep)
    (paths : ∀ k, Path k) (lookup : LookupHolds) : HeadlineFor :=
  fun fetch L A premises => ⟨initial fetch L A premises, framed fetch L A premises,
    insertStep_of_paths run paths fetch L A premises, lookup fetch L A premises⟩

/-- `Headline` is `HeadlineFor` with the invariant forgotten. -/
theorem headline_of_for (h : HeadlineFor) : Headline :=
  fun fetch L A premises => ⟨Inv L A, h fetch L A premises⟩

/-- `HeadlineFor` is `HeadlineExplicit`: `Inv` is `Related`. -/
theorem explicit_of_for (h : HeadlineFor) : HeadlineExplicit := h

/-- WHAT THE FOUR PACKAGES ADD UP TO. Every hypothesis is one package's
acceptance theorem. -/
theorem signed_of_parts
    -- package 1: the source side and the invariant's algebra
    (run : RunIsStep) (initial : InitialHolds) (framed : FramedHolds) (lookup : LookupHolds)
    (exclusion1 : ExclusionOne) (exclusion2 : ExclusionTwo)
    -- package 2: the trunk and the paths that end above the placement
    (tooLong : PathTooLong) (rootNoMem : PathRootNoMem) (root : PathRoot) (exact : PathExact)
    (nodeNoMem : PathNodeNoMem) (child : PathChild) (trunk : TrunkHolds)
    -- package 3: the paths below the placement
    (cover : PathCover) (splitNoMem : PathSplitNoMem) (split : PathSplit)
    -- package 4: the services and the witness
    (alloc : AllocRule) (free : FreeRule) (witness : WitnessHolds) : Signed := by
  have h : HeadlineFor := headlineFor_of_parts initial framed run
    (paths_of_parts nodeBelowTop framed alloc free trunk tooLong rootNoMem root exact nodeNoMem child cover splitNoMem split)
    lookup
  exact ⟨headline_of_for h, witness h, exclusion1 h, exclusion2 h⟩

#print axioms signed_of_parts
end Binary.Statements.C1.Proof
