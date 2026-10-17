import Leanux.Proofs.WG.Progress.ControlLaws

namespace Leanux.Proofs.WG.Progress
open Leanux

variable {σ : Type}
variable [MonadLiftT WG.M (StateT σ (Except Stop))]
variable [MonadLiftT AmbientM (StateT σ (Except Stop))]

/-- Instantiating the generic law gives exactly the original worker iteration,
including both arbitrary callbacks and their concrete intermediate states. -/
theorem workerIter_control (worker : Worker) (pid : Option Nat) (step afterItem : StateT σ (Except Stop) Bool) :
    workerIter worker pid step afterItem = Control.iterate step afterItem := rfl

theorem workerIter_empty (worker : Worker) (pid : Option Nat)
    (step afterItem : StateT σ (Except Stop) Bool) (w v : σ)
    (empty : step.run w = .ok (false, v)) :
    (workerIter worker pid step afterItem).run w = .ok (.ended, v) := by
  simp only [workerIter, StateT.run_bind, empty]
  rfl

theorem workerIter_productive (worker : Worker) (pid : Option Nat)
    (step afterItem : StateT σ (Except Stop) Bool) (w v : σ)
    (item : step.run w = .ok (true, v)) :
    (workerIter worker pid step afterItem).run w =
      (afterItem.run v >>= fun out =>
        pure (if out.1 then .yielded else .continued, out.2)) := by
  simp only [workerIter, StateT.run_bind, item]
  rfl

end Leanux.Proofs.WG.Progress
