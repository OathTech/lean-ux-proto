import C1BelowStep
import C1BelowInv

/-! Result C1, work package 3, rollback: what `StepFacts` says of a run in
case `splitNoMem`, in the terms the machine segment consumes. -/
namespace Binary.Statements.C1.Proof.Undo
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1

theorem slotOf_rootSlot (d : Device) (family : Nat) :
    slotOf (bump d) (rootSlot family) = rootOf d family := by
  unfold rootSlot rootOf
  split <;> rfl

theorem widthOf_le (family : Nat) : widthOf family ≤ 128 := by
  unfold widthOf
  split <;> decide

/-- Case `splitNoMem`: the common prefix with the node below is strictly
shorter than the new prefix, the answer is `-ENOMEM`, the device is the
rolled-back one, and the second pending record (site 79) says "refused". -/
theorem rollback_case {w w' : World} {family key cidr pid : Nat} {answer : Int} {d : Device}
    {stream : List HiddenRecord} {placed : Option NodeId} {exact : Bool} {st : Step}
    (facts : StepFacts w family key cidr pid answer w' d stream placed exact st)
    (case : st.case = .splitNoMem) {downId : NodeId} {down : AipNode}
    (lower : below (bump d) (rootOf d family) key placed = some downId)
    (present : (bump d).nodes.get? downId = some down) :
    AllowedipsRelation.common (widthOf family) down.bits key < cidr ∧ cidr ≤ widthOf family ∧
    answer = -ENOMEM ∧ st.device = rollbackDevice d family key cidr pid ∧
    ∃ first second rest, stream = first :: second :: rest ∧ second.site = 79 ∧
      stream.drop st.consumed = rest ∧ second.bytes.head? = some 0 := by
  obtain ⟨rootId,downId',down',rest,b⟩ := step_below facts.model (.inr (.inr case))
  have root := b.root
  rw [slotOf_rootSlot] at root
  rw [root] at lower
  cases Option.some.inj (lower.symm.trans b.hasBelow)
  cases Option.some.inj (present.symm.trans b.hasDown)
  obtain ⟨differ,refused,result,device⟩ := b.rollback case
  obtain ⟨first,second,tail,shape,_,site,dropped,_,outcome⟩ := facts.two_records (.inr case)
  refine ⟨?_,b.fits,facts.result.trans result,device,first,second,tail,shape,site,dropped,?_⟩
  · simp only [leastOf,Nat.min_def] at differ
    split at differ <;> omega
  · have outcomes := b.first
    rw [shape] at outcomes
    simp only [List.map_cons,List.cons.injEq] at outcomes
    rcases outcome with zero | one
    · exact zero
    · exfalso
      apply refused
      rw [←outcomes.2]
      simp [one]

#print axioms rollback_case
end Binary.Statements.C1.Proof.Undo
