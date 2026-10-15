import Leanux.Kernel.Defs

/-! Generic state/error control laws. Arbitrary callbacks are not claimed to be
WireGuard-local. The concrete original worker bridge is in ControlSource. -/
namespace Leanux.Proofs.WG.Progress.Control
open Leanux

def iterate {σ ε : Type} (step afterItem : StateT σ (Except ε) Bool) : StateT σ (Except ε) IterResult := do
  if !(← step) then return .ended
  return if ← afterItem then .yielded else .continued

theorem empty {σ ε : Type} (step afterItem : StateT σ (Except ε) Bool) (w v : σ)
    (h : step.run w = .ok (false, v)) :
    (iterate step afterItem).run w = .ok (.ended, v) := by
  simp only [iterate, StateT.run_bind, h]
  rfl

theorem productive {σ ε : Type} (step afterItem : StateT σ (Except ε) Bool) (w v : σ)
    (h : step.run w = .ok (true, v)) :
    (iterate step afterItem).run w =
      (afterItem.run v >>= fun out => pure (if out.1 then .yielded else .continued, out.2)) := by
  simp only [iterate, StateT.run_bind, h]
  rfl

end Leanux.Proofs.WG.Progress.Control
