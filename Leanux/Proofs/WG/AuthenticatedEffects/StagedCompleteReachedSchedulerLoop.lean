import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerSource

/-! Literal successful yield prefixes of the scheduler's finite loops.
The remaining source is fixed by the original list suffix; a stopped step has
only its actual entry world and failed result, never an invented return state. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler
open Leanux Leanux.Proofs.Logged CausalJournal

inductive Yields (step : Nat → σ → PrefixM Event (ForInStep σ)) :
    List Nat → σ → World → List Event → σ → World → List Event → Prop where
  | nil : Yields step [] acc w history acc w history
  | cons (run : runPrefix (step index acc) w history = (.ok (.yield next,u),middle))
      (tail : Yields step indices next u middle final v last) :
      Yields step (index :: indices) acc w history final v last

theorem Yields.run (path : Yields step indices acc w history final v last) :
    runPrefix (forIn indices acc step) w history = (.ok (final,v),last) := by
  induction path with
  | nil => rfl
  | cons performed tail ih =>
    rw [List.forIn_cons,runPrefix_bind,performed]
    exact ih

theorem Yields.continue {σ α : Type} {step : Nat → σ → PrefixM Event (ForInStep σ)}
    {acc final : σ} (path : Yields step done acc w history final v last)
    (remaining : List Nat) (finish : σ → PrefixM Event α) :
    runPrefix (forIn (done ++ remaining) acc step >>= finish) w history =
      runPrefix (forIn remaining final step >>= finish) v last := by
  induction path with
  | nil => rfl
  | cons performed tail ih =>
    simp only [List.cons_append,List.forIn_cons,bind_assoc]
    rw [runPrefix_bind,performed]
    exact ih

theorem Yields.carrier (path : Yields step indices acc w history final v last)
    (checked : ∀ index acc, CompleteProduct.Checked (step index acc))
    (before : CompleteProduct.Carrier history w) : CompleteProduct.Carrier last v := by
  induction path with
  | nil => exact before
  | @cons index acc w history next u middle indices final v last performed tail ih =>
    have kept := (checked index acc w history before).choose_spec.2.2
    rw [performed] at kept
    exact ih kept

/-- A failed finite loop identifies its actual first failing iteration after
only completed yields; no post-world is inferred from the exception. -/
theorem loop_failed (step : Nat → σ → PrefixM Event (ForInStep σ))
    (indices : List Nat) (acc : σ) (w : World) (history : List Event)
    (failed : runPrefix (forIn indices acc step) w history = (.error reason,last)) :
    ∃ done index remaining next u middle,
      indices = done ++ index :: remaining ∧
      Yields step done acc w history next u middle ∧
      runPrefix (step index next) u middle = (.error reason,last) := by
  induction indices generalizing acc w history with
  | nil => simp only [List.forIn_nil,runPrefix_pure] at failed; cases failed
  | cons index indices ih =>
    rw [List.forIn_cons,runPrefix_bind] at failed
    cases performed : runPrefix (step index acc) w history with
    | mk result middle =>
      rw [performed] at failed
      cases result with
      | error error =>
        cases failed
        exact ⟨[],index,indices,acc,w,history,rfl,.nil,performed⟩
      | ok out =>
        obtain ⟨decision,u⟩ := out
        cases decision with
        | done final => simp only [runPrefix_pure] at failed; cases failed
        | yield next =>
          obtain ⟨done,j,remaining,final,v,current,shape,path,stopped⟩ := ih next u middle failed
          exact ⟨index :: done,j,remaining,final,v,current,by simp only [List.cons_append,shape],
            .cons performed path,stopped⟩

/-- A real failed loop retains the carrier at the actual failing iteration's
entry after its literal completed prefix. No exception is assigned a world. -/
theorem loop_failed_carrier (step : Nat → σ → PrefixM Event (ForInStep σ))
    (checked : ∀ index acc, CompleteProduct.Checked (step index acc))
    (indices : List Nat) (acc : σ) (w : World) (history : List Event)
    (before : CompleteProduct.Carrier history w)
    (failed : runPrefix (forIn indices acc step) w history = (.error reason,last)) :
    ∃ done index remaining next u middle,
      indices = done ++ index :: remaining ∧
      Yields step done acc w history next u middle ∧
      CompleteProduct.Carrier middle u ∧
      runPrefix (step index next) u middle = (.error reason,last) := by
  obtain ⟨done,index,remaining,next,u,middle,shape,path,stopped⟩ := loop_failed step indices acc w history failed
  exact ⟨done,index,remaining,next,u,middle,shape,path,path.carrier checked before,stopped⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler
