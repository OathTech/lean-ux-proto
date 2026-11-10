import C1BelowStep
import C1BelowInv

/-! Result C1, work package 3, the split path: what the step facts say of a
run in case `split`, in the form the machine segments consume. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1

theorem slotOf_rootSlot (d : Device) (family : Nat) :
    slotOf (bump d) (rootSlot family) = rootOf d family := by
  unfold rootSlot rootOf
  cases h : family == 4 <;> simp [slotOf,bump]

/-- Case `split`: the answer is 0, two records are consumed, the second of
site 79 with outcome 1, and the common prefix with the node below the
placement is strictly shorter than the new prefix. -/
theorem split_source {w w' : World} {family key cidr pid : Nat} {answer : Int} {d : Device}
    {stream : List HiddenRecord} {placed : Option NodeId} {exact : Bool} {st : Step}
    (facts : StepFacts w family key cidr pid answer w' d stream placed exact st)
    (case : st.case = .split) :
    answer = 0 ∧ cidr ≤ widthOf family ∧
    (∃ first second rest, stream = first :: second :: rest ∧ second.site = 79 ∧
      second.bytes.head? = some 1 ∧ stream.drop st.consumed = rest) ∧
    ∀ downId down, below (bump d) (rootOf d family) key placed = some downId →
      (bump d).nodes.get? downId = some down →
      AllowedipsRelation.common (widthOf family) down.bits key < cidr := by
  obtain ⟨rootId,downId',down',rest',inverted⟩ := step_below facts.model (.inr (.inl case))
  obtain ⟨differ,⟨tail,second⟩,zero,_⟩ := inverted.split case
  obtain ⟨first,next,rest,shape,_,site,dropped,_,_⟩ := facts.two_records (.inl case)
  refine ⟨facts.result.trans zero,inverted.fits,⟨first,next,rest,shape,site,?_,dropped⟩,?_⟩
  · have outcomes := inverted.first
    rw [second,shape] at outcomes
    simp only [List.map_cons,List.cons.injEq] at outcomes
    exact eq_of_beq outcomes.2.1
  · intro downId down found present
    have located := inverted.hasBelow
    have root := inverted.root
    rw [slotOf_rootSlot] at root
    rw [root] at found
    have same : downId = downId' := Option.some.inj (found.symm.trans located)
    subst same
    have node : down = down' := Option.some.inj (present.symm.trans inverted.hasDown)
    subst node
    unfold leastOf at differ
    omega

#print axioms split_source
end Binary.Statements.C1.Proof
