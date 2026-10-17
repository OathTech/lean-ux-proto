import Leanux.Proofs.WG.Noise.TagSequenceSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- Every normal finite execution yields a linked history of the original
seven operations, with complete before/after projection and all-peer effects.
No residency, readiness, owner or reference-budget premise is assumed. -/
theorem observedTagSequence_chain (operations : List TagOperation) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observedTagSequence operations) (fun s => s = entry)
      (fun receipts final => TagChain entry operations receipts final) := by
  induction operations generalizing entry with
  | nil =>
    intro g ambient receipts final after pre run
    cases run
    rw [← pre]
    exact .nil _
  | cons operation operations ih =>
    intro g ambient receipts final after pre run
    subst entry
    simp only [observedTagSequence,observedTagOperation,bind_assoc] at run
    change (((runTagOperation operation).run g).run ambient >>= fun ((result,next),inputs) =>
      ((observedTagSequence operations).run next).run inputs >>= fun ((tail,finish),finishInputs) =>
      Except.ok ((TagReceipt.mk operation (Campaign2.snapshot g ambient) result
        (Campaign2.snapshot next inputs) :: tail,finish),finishInputs)) = _ at run
    cases actual : ((runTagOperation operation).run g).run ambient with
    | error stop => rw [actual] at run; cases run
    | ok out =>
      obtain ⟨⟨result,next⟩,inputs⟩ := out
      rw [actual] at run
      change (((observedTagSequence operations).run next).run inputs >>= _) = _ at run
      cases later : ((observedTagSequence operations).run next).run inputs with
      | error stop => rw [later] at run; cases run
      | ok out =>
        obtain ⟨⟨tail,finish⟩,finishInputs⟩ := out
        rw [later] at run
        cases run
        exact .cons ⟨operation,Campaign2.snapshot g ambient,result,Campaign2.snapshot next inputs⟩
          operations tail (Campaign2.snapshot final after)
          (runTagOperation_effect operation (Campaign2.snapshot g ambient)
            g ambient result next inputs rfl actual)
          (ih (Campaign2.snapshot next inputs) next inputs tail final after rfl later)

end Leanux.Proofs.WG.Noise
