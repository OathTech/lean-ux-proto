import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionPrimitiveSource

/-! Every primitive in the fixed encryption preparation tree preserves WG.
These source frames transport the original account to each actual point;
they do not infer an intermediate world from a later successful encryption. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionPrimitive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
variable {α : Type} {action : Leanux.M α} {shape : Shape action}

theorem Shape.normal (shape : Shape action) (performed : action.run w=.ok (value,v)) : v.wg=w.wg := by
  induction shape generalizing w v with
  | pure result=>cases performed;rfl
  | primitive primitive=>exact (ProjectedAction.iff_run _ _ _).mp primitive.frame w value v performed
  | @bind α β body next head tail ihHead ihTail=>
    rw [StateT.run_bind] at performed
    cases leading : body.run w with
    | error stop=>rw [leading] at performed;cases performed
    | ok pair=>
      obtain ⟨first,u⟩:=pair
      rw [leading] at performed
      exact (ihTail first performed).trans (ihHead leading)

/-- Each declared primitive point retains the full WG projection of its
original preparation entry, including the entry of a primitive that stops. -/
theorem Point.same_wg (point : Point shape w v) : v.wg=w.wg := by
  induction point with
  | entry shape=>rfl
  | returned shape performed=>exact shape.normal performed
  | left tail point ih=>exact ih
  | right head tail leading point ih=>exact ih.trans (head.normal leading)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionPrimitive
