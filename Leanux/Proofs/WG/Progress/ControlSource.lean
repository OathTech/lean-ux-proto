import Leanux.Proofs.WG.Progress.ControlLaws

namespace Leanux.Proofs.WG.Progress
open Leanux

/-- Instantiating the generic law gives exactly the original worker iteration,
including both arbitrary callbacks and their concrete intermediate states. -/
theorem workerIter_control (worker : Worker) (pid : Option Nat) (step afterItem : M Bool) :
    workerIter worker pid step afterItem = Control.iterate step afterItem := rfl

theorem workerIter_empty (worker : Worker) (pid : Option Nat)
    (step afterItem : M Bool) (w v : World)
    (empty : step.run w = .ok (false, v)) :
    (workerIter worker pid step afterItem).run w = .ok (.ended, v) := by
  simp only [workerIter, StateT.run_bind, empty, Except.bind]
  rfl

theorem workerIter_productive (worker : Worker) (pid : Option Nat)
    (step afterItem : M Bool) (w v : World)
    (item : step.run w = .ok (true, v)) :
    (workerIter worker pid step afterItem).run w =
      (afterItem.run v >>= fun out =>
        pure (if out.1 then .yielded else .continued, out.2)) := by
  simp only [workerIter, StateT.run_bind, item, Except.bind]
  rfl

end Leanux.Proofs.WG.Progress
