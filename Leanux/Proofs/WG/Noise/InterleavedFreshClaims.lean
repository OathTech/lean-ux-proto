import Leanux.Proofs.WG.Noise.InterleavedFreshSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- The source receipt uses each actual actor and each preceding full projected
boundary. A failed call returns its first Stop, not a fabricated partial chain. -/
theorem observedInterleavedFreshSequence_chain (tracked : PeerId)
    (operations : List InterleavedFreshOperation) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observedInterleavedFreshSequence operations) (fun s => s = entry)
      (fun receipts final => InterleavedFreshChain tracked entry operations receipts final) := by
  induction operations generalizing entry with
  | nil =>
    intro g ambient receipts final after pre run
    cases run
    rw [← pre]
    exact .nil _
  | cons scheduled operations ih =>
    obtain ⟨actor,operation⟩ := scheduled
    intro g ambient receipts final after pre run
    subst entry
    simp only [observedInterleavedFreshSequence,observedFreshOperation,bind_assoc] at run
    change (((runFreshOperation actor operation).run g).run ambient >>= fun ((result,next),inputs) =>
      ((observedInterleavedFreshSequence operations).run next).run inputs >>= fun ((tail,finish),finishInputs) =>
        Except.ok ((InterleavedFreshReceipt.mk actor
          (FreshReceipt.mk operation (Campaign2.snapshot g ambient) result
            (Campaign2.snapshot next inputs)) :: tail,finish),finishInputs)) = _ at run
    cases actual : ((runFreshOperation actor operation).run g).run ambient with
    | error stop => rw [actual] at run; cases run
    | ok out =>
      obtain ⟨⟨result,next⟩,inputs⟩ := out
      rw [actual] at run
      change (((observedInterleavedFreshSequence operations).run next).run inputs >>= _) = _ at run
      cases later : ((observedInterleavedFreshSequence operations).run next).run inputs with
      | error stop => rw [later] at run; cases run
      | ok out =>
        obtain ⟨⟨tail,finish⟩,finishInputs⟩ := out
        rw [later] at run
        cases run
        exact .cons ⟨actor,⟨operation,Campaign2.snapshot g ambient,result,Campaign2.snapshot next inputs⟩⟩
          operations tail (Campaign2.snapshot final after)
          (runFreshOperation_interleaved_effect tracked actor operation (Campaign2.snapshot g ambient)
            g ambient result next inputs rfl actual)
          (ih (Campaign2.snapshot next inputs) next inputs tail final after rfl later)

/-- The original nine native operations may act on arbitrary peers. Successful
confirmation IDs for the tracked peer remain distinct under its sole initial
next/cursor bound. Shared key IDs, absent peers and all source Stops remain.
This is neither all-actor distinctness nor allocation residency, recreation,
reset or initialized-driver lifetime coverage. -/
theorem interleaved_fresh_confirmation_history (tracked : PeerId)
    (operations : List InterleavedFreshOperation) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observedInterleavedFreshSequence operations)
      (fun s => s = entry ∧ FreshNextBound tracked entry)
      (fun receipts final => InterleavedFreshChain tracked entry operations receipts final ∧
        (interleavedConfirmedIds tracked receipts).Nodup) := by
  intro g ambient receipts final after pre run
  have chain := observedInterleavedFreshSequence_chain tracked operations entry
    g ambient receipts final after pre.1 run
  have distinct := (chain.preserves (freshSeen_initial tracked entry pre.2)).distinct
  exact ⟨chain,by simpa using distinct⟩

end Leanux.Proofs.WG.Noise
