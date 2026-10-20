import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReadGetterSource

/-! Frames for getter source points. Fixed failure calls never return a
world or clock; every other constructor preserves both by its operational type. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReadGetter
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues

theorem normal (source : Shape action)
    (performed : (action.run w).run a=.ok ((value,v),b)) : v=w ∧ b=a := by
  induction source generalizing w a v b with
  | pure value => cases performed;exact ⟨rfl,rfl⟩
  | read => cases performed;exact ⟨rfl,rfl⟩
  | invariant message => cases performed
  | unsupported message => cases performed
  | bind head tail ihHead ihTail =>
      simp only [StateT.run_bind] at performed
      rename_i body next
      cases leading : (body.run w).run a with
      | error reason => rw [leading] at performed;cases performed
      | ok pair =>
          obtain ⟨⟨x,u⟩,c⟩ := pair
          rw [leading] at performed
          obtain ⟨rfl,rfl⟩ := ihHead leading
          exact ihTail x performed

theorem Point.state (point : Point source w a v b) : v=w ∧ b=a := by
  induction point with
  | entry source => exact ⟨rfl,rfl⟩
  | returned source performed => exact normal source performed
  | left tail point ih => exact ih
  | right head tail leading point ih =>
      obtain ⟨rfl,rfl⟩ := normal head leading
      exact ih

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReadGetter
