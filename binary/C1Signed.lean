import C1Assembly
import C1Source
import C1TrunkClosed
import C1Below
import C1Service

/-! Result C1, integration: the four packages joined.

`signed_of_referenced_and_witness` is `Signed` from the two interface
propositions nobody has proved yet:

* `ReferencedHolds` (package 1's owner): the reference clause revision 3 of
  the statement added and revision 4 re-paired with `peerGetMaybeZero`;
* `WitnessHolds` (package 4's owner): the witness as revision 3 restated it.

Every other hypothesis of `C1Assembly.signed_of_parts` is discharged by a
package's theorem. The `example`s are type ascriptions: each interface
proposition against the theorem that proves it, so the build fails if a
statement or a proof drifts. The hand-over for the two open propositions is
`binary/Statements/C1/proof/OPEN.md`. Nothing here is a registered headline
yet. -/
namespace Binary.Statements.C1.Proof
open Binary.Statements.C1

/-! ## Each interface proposition and the theorem that proves it -/

-- package 1: the source side
example : RunIsStep := runIsStep
example : InitialHolds := initialHolds
example : FramedHolds := framedHolds
example : LookupHolds := lookupHolds
example : ExclusionOne := exclusionOne
example : ExclusionTwo := exclusionTwo
-- the node bound, from the signed text since revision 3
example : NodeBelowTop := nodeBelowTop
-- package 2: the trunk and the paths that end above the placement
example : PathTooLong := pathTooLong
example : PathRootNoMem := pathRootNoMem
example : PathRoot := pathRoot
example : PathExact := pathExact
example : PathNodeNoMem := pathNodeNoMem
example : PathChild := pathChild
example : TrunkHolds := trunkHolds
example : TrunkPlusHolds := trunkToNodePlus
-- package 3: the paths below the placement, from the strengthened trunk
example : PathCoverPlus := pathCover_plus
example : PathSplitPlus := pathSplit_plus
example : PathSplitNoMemPlus := pathSplitNoMem_plus
-- package 4: the service rules, the callbacks from the image, the premises met
example : AllocRule := allocRule
example : FreeRule := freeRule
example : Cmp1FromImage := cmp1FromImage
example : Cmp8FromImage := cmp8FromImage
example : PremisesMet := premisesMet

/-! ## The headline with the invariant fixed: closed -/

/-- The four clauses of the headline for `Inv` that do not mention the
reference clause, with no hypothesis left. `WitnessHolds`, `ExclusionOne`
and `ExclusionTwo` take this. -/
theorem headlineFor : HeadlineFor :=
  headlineFor_of_parts initialHolds framedHolds runIsStep
    (paths_of_parts nodeBelowTop framedHolds allocRule freeRule trunkToNodePlus pathTooLong pathRootNoMem
      pathRoot pathExact pathNodeNoMem pathChild pathCover_plus pathSplitNoMem_plus pathSplit_plus)
    lookupHolds

/-- The two exclusions, closed. -/
theorem insertThenLookup : InsertThenLookup := exclusionOne headlineFor
theorem failedInsertInvisible : FailedInsertInvisible := exclusionTwo headlineFor

/-! ## What is left -/

/-- `Signed` from exactly the two open propositions. -/
theorem signed_of_referenced_and_witness : ReferencedHolds → WitnessHolds → Signed :=
  fun referenced witness =>
    signed_of_parts runIsStep initialHolds framedHolds referenced lookupHolds exclusionOne exclusionTwo
      pathTooLong pathRootNoMem pathRoot pathExact pathNodeNoMem pathChild trunkToNodePlus
      pathCover_plus pathSplitNoMem_plus pathSplit_plus allocRule freeRule witness

#print axioms headlineFor
#print axioms signed_of_referenced_and_witness
end Binary.Statements.C1.Proof
