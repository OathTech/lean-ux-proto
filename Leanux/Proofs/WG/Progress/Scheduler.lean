import Leanux.Env.Batch
import Leanux.Proofs.WG.Noise.Basic

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.Env Leanux.Proofs.WG.Noise

/-- The exact probe result, including errors that must propagate. -/
def probeResult (w : World) : Except Stop (Unit × World) → Except Stop (Bool × World)
  | .ok _ => .ok (true, w)
  | .error (.hidden _) => .ok (false, w)
  | .error e => .error e

theorem consistent_exact (a : Activation) (w : World) :
    (Activation.consistent a).run w = probeResult w ((Activation.run a).run w) := by
  simp only [Activation.consistent, StateT.run_bind, StateT.run_get, pure_bind]
  cases h : (Activation.run a).run w with
  | ok out => rfl
  | error e => cases e <;> rfl

theorem consistent_success_iff (a : Activation) (w v : World) :
    (Activation.consistent a).run w = .ok (true, v) ↔
      v = w ∧ ∃ out, (Activation.run a).run w = .ok out := by
  rw [consistent_exact]
  cases h : (Activation.run a).run w with
  | ok out => simp [probeResult, eq_comm]
  | error e => cases e <;> simp [probeResult, eq_comm]

theorem consistent_hidden_iff (a : Activation) (w v : World) :
    (Activation.consistent a).run w = .ok (false, v) ↔
      v = w ∧ ∃ message, (Activation.run a).run w = .error (.hidden message) := by
  rw [consistent_exact]
  cases h : (Activation.run a).run w with
  | ok out => simp [probeResult, eq_comm]
  | error e => cases e <;> simp [probeResult, eq_comm]

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
