import Leanux.Proofs.WG.Noise.FreshHistorySource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG


/-- The actual finite execution links every receipt to the preceding native
state, without assuming any successful prefix. -/
theorem observedFreshSequence_chain (pid : PeerId) (operations : List FreshOperation)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observedFreshSequence pid operations) (fun s => s = entry)
      (fun receipts final => FreshChain pid entry operations receipts final) := by
  induction operations generalizing entry with
  | nil =>
    intro g ambient receipts final after pre run
    cases run
    rw [← pre]
    exact .nil _
  | cons operation operations ih =>
    intro g ambient receipts final after pre run
    subst entry
    simp only [observedFreshSequence,observedFreshOperation,bind_assoc] at run
    change (((runFreshOperation pid operation).run g).run ambient >>= fun ((result,next),inputs) =>
      ((observedFreshSequence pid operations).run next).run inputs >>= fun ((tail,finish),finishInputs) =>
      Except.ok ((FreshReceipt.mk operation (Campaign2.snapshot g ambient) result
        (Campaign2.snapshot next inputs) :: tail,finish),finishInputs)) = _ at run
    cases actual : ((runFreshOperation pid operation).run g).run ambient with
    | error stop => rw [actual] at run; cases run
    | ok out =>
      obtain ⟨⟨result,next⟩,inputs⟩ := out
      rw [actual] at run
      change (((observedFreshSequence pid operations).run next).run inputs >>= _) = _ at run
      cases later : ((observedFreshSequence pid operations).run next).run inputs with
      | error stop => rw [later] at run; cases run
      | ok out =>
        obtain ⟨⟨tail,finish⟩,finishInputs⟩ := out
        rw [later] at run
        cases run
        exact .cons ⟨operation,Campaign2.snapshot g ambient,result,Campaign2.snapshot next inputs⟩
          operations tail (Campaign2.snapshot final after)
          (runFreshOperation_effect pid operation (Campaign2.snapshot g ambient)
            g ambient result next inputs rfl actual)
          (ih (Campaign2.snapshot next inputs) next inputs tail final after rfl later)

/-- Successful confirmations have distinct numeric IDs throughout a finite
sequence of the four original calls. The explicit initial next/cursor bound
is the only state premise. This language excludes direct reinstallation,
peer recreation and device reset; it asserts neither global reachability nor
allocation-lifetime identity outside this finite execution. -/
theorem fresh_confirmation_history (pid : PeerId) (operations : List FreshOperation)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observedFreshSequence pid operations)
      (fun s => s = entry ∧ FreshNextBound pid entry)
      (fun receipts final => FreshChain pid entry operations receipts final ∧
        (freshConfirmedIds receipts).Nodup) := by
  intro g ambient receipts final after pre run
  have chain := observedFreshSequence_chain pid operations entry
    g ambient receipts final after pre.1 run
  have distinct := (chain.preserves (freshSeen_initial pid entry pre.2)).distinct
  exact ⟨chain,by simpa using distinct⟩

end Leanux.Proofs.WG.Noise
