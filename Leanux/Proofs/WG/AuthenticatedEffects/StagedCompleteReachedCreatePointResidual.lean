import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointExecution

/-! Positions belong to the canonical create source. The lower adapter keeps
the exact product-world continuation and projects only its final WG/ambient
result; native intermediate worlds are never inferred from an endpoint. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
set_option maxHeartbeats 600000

inductive Point : {α : Type} → {action : PrefixM Event α} → Shape action →
    World → History → {β : Type} → PrefixM Event β → World → History → PrefixM Event α → Type 1 where
  | entry (shape : Shape action) : Point shape w h action w h action
  | returned (shape : Shape action) (performed : runPrefix action w h=(.ok (value,u),middle)) :
      Point shape w h (pure value) u middle (pure value)
  | left {body : PrefixM Event α} {next : α → PrefixM Event β} {head : Shape body}
      (tail : ∀ value, Shape (next value)) (point : Point head w h leaf u middle remaining) :
      Point (.bind head tail) w h leaf u middle (remaining >>= next)
  | right {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀ value, Shape (next value))
      (leading : runPrefix body w h=(.ok (value,v),prior))
      (point : Point (tail value) v prior leaf u middle remaining) :
      Point (.bind head tail) w h leaf u middle remaining
  | marked (label : Label) (point : Point shape w h leaf u middle remaining) :
      Point (.marked label shape) w h leaf u middle remaining

theorem Point.residual {shape : Shape action} (point : Point shape w h leaf u middle remaining) :
    runPrefix action w h=runPrefix remaining u middle := by
  induction point with
  | entry=>rfl
  | returned shape performed=>exact performed
  | left tail point ih=>rw [runPrefix_bind,runPrefix_bind,ih]
  | right head tail leading point ih=>rw [runPrefix_bind,leading]; exact ih
  | marked label point ih=>exact ih

theorem Point.stopped {shape : Shape action} (point : Point shape w h leaf u middle remaining)
    (failed : runPrefix remaining u middle=(.error stop,last)) :
    runPrefix action w h=(.error stop,last) := point.residual.trans failed

theorem Point.normal {shape : Shape action} (point : Point shape w h leaf u middle remaining)
    (returned : runPrefix remaining u middle=(.ok (value,v),last)) :
    runPrefix action w h=(.ok (value,v),last) := point.residual.trans returned

theorem Point.lowered
    (point : Point (createShape pid items) (NativeAdapter.world w a) h leaf u middle remaining) :
    runWGPrefix (CausalJournal.create pid items) w a h=
      ((runPrefix remaining u middle).1.map (fun (value,v)=>((value,v.wg),v.ambient)),
        (runPrefix remaining u middle).2) := by
  rw [lower_factor,runWGPrefix,NativeAdapter.run_lower,point.residual]

noncomputable def Point.cast {action other : PrefixM Event α} (equal : action=other)
    {shape : Shape other} (point : Point shape w h leaf u middle remaining) :
    Point (equal.symm ▸ shape) w h leaf u middle remaining := by cases equal; exact point

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
