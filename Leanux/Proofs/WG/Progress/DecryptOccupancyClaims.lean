import Leanux.Proofs.WG.Progress.DecryptOccupancySource

/-! Normal original-iteration effects and coherent-ring occupancy adequacy.
The total-return contract is for inspection: it does not assert success or
finite evaluation of every underlying callback, nor record-suffix progress. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.DecryptOccupancy
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
open Leanux.Proofs.WG.Queues

theorem original_iteration (a : Activation) (worker : a.worker = .decryptWorker)
    (deviceIndex capacity batch : Nat) (live : List SkbId) :
    Campaign2.Product.Ensures (Activation.iter a)
      (Rep deviceIndex capacity batch live)
      (fun value after => (value = .ended ↔ live = []) ∧ Rep deviceIndex capacity batch live.tail after) := by
  intro w value v pre run
  exact iteration_rep a worker deviceIndex capacity batch live w v value pre run

theorem original_activation (a : Activation) (worker : a.worker = .decryptWorker)
    (deviceIndex capacity batch : Nat) (live : List SkbId) :
    Campaign2.Product.Returns (observedActivationExit a)
      (Rep deviceIndex capacity batch live)
      (fun audit _ => NoExhaustion audit ∧ ActivationExitFacts a audit) := by
  intro entry pre
  exact ⟨_,entry,rfl,activation_no_exhaustion a worker deviceIndex capacity batch live entry pre,
    activationExitRun_facts a entry⟩


end Leanux.Proofs.WG.Progress.DecryptOccupancy
