import Leanux.Proofs.WG.Lifetimes.BatchScheduler

/-! Copied-world consistency trials, including every candidate tested before a
non-hidden Stop. Each trial starts from the caller's same World and history;
its speculative accesses are certified separately, never committed or rolled back. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def activationTrialDecision (a : Activation) (w : World) (h : List LifetimeEvent) : Except Stop Bool :=
  match (runPrefix (activationRunPrefix a) w h).1 with
  | .ok _ => .ok true
  | .error (.hidden _) => .ok false
  | .error e => .error e

theorem activationTrialDecision_eq (a : Activation) (w : World) (h : List LifetimeEvent) :
    (Env.Activation.consistent a).run w =
      (activationTrialDecision a w h).map (fun b => (b, w)) := by
  have he := congrArg Prod.fst (activationConsistent_trial a w h)
  simpa only [runPrefix_lift] using he.trans (by
    unfold activationTrialDecision
    cases (runPrefix (activationRunPrefix a) w h).1 with
    | ok out => rfl
    | error e => cases e <;> rfl)

private theorem trialFilterAux (xs acc : List Activation) (w : World) (h : List LifetimeEvent) :
    (List.filterAuxM Env.Activation.consistent xs acc).run w =
      (List.filterAuxM (fun a => activationTrialDecision a w h) xs acc).map (fun ys => (ys, w)) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.filterAuxM, StateT.run_bind, activationTrialDecision_eq a w h]
    cases hr : activationTrialDecision a w h <;> simp [Except.map, ih]

/-- Original filterM order and early failure are reproduced by the separately
observed trials. Hidden mismatch is an ordinary false decision; any other Stop
terminates the same filter. No candidate is assumed to have been selected. -/
theorem activationTrials_filter (xs : List Activation) (w : World) (h : List LifetimeEvent) :
    (xs.filterM Env.Activation.consistent).run w =
      (xs.filterM (fun a => activationTrialDecision a w h)).map (fun ys => (ys, w)) := by
  simp only [List.filterM, StateT.run_bind, trialFilterAux xs [] w h]
  cases hr : List.filterAuxM (fun a => activationTrialDecision a w h) xs [] <;> simp [Except.map]

/-- Every candidate has a safe trial prefix from an allocation-valid entry,
including false and non-hidden-error candidates. Together with filter equality,
this covers all evaluated candidates, without asserting unevaluated ones ran. -/
theorem activationTrials_safe (xs : List Activation) (w : World) (h : List LifetimeEvent)
    (hi : AllocationInv h w.wg) :
    ∀ a ∈ xs, LifetimeEvent.Safe (runPrefix (activationRunPrefix a) w h).2 := by
  intro a _
  exact (activationRunPrefix_allocation a w h hi).choose_spec.2.1

end Leanux.Proofs.WG.Lifetimes
