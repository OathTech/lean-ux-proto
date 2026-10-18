import Leanux.Proofs.WG.Queues.RxRingScheduler

/-! Trials certify their own RX-ring prefixes on the caller's copied World.
Neither a trial's resulting World nor its events enter the committed journal.
The original ordered filter and first non-hidden failure are retained exactly. -/
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem activationConsistent_trial (a : Activation) (w : World) (h : List Event) :
    runPrefix (liftPrefix (Env.Activation.consistent a) : Obs Bool) w h =
      ((match (runPrefix (activationRun a) w h).1 with
        | .ok _ => .ok (true, w)
        | .error (.hidden _) => .ok (false, w)
        | .error e => .error e), h) := by
  rw [activationRun_erases a w h]
  simp only [runPrefix_lift, Env.Activation.consistent, StateT.run_bind, StateT.run_get, pure_bind]
  cases (Env.Activation.run a).run w with
  | ok out => rfl
  | error e => cases e <;> rfl

def trialDecision (a : Activation) (w : World) (h : List Event) : Except Stop Bool :=
  match (runPrefix (activationRun a) w h).1 with
  | .ok _ => .ok true
  | .error (.hidden _) => .ok false
  | .error e => .error e

theorem trialDecision_eq (a : Activation) (w : World) (h : List Event) :
    (Env.Activation.consistent a).run w =
      (trialDecision a w h).map (fun b => (b, w)) := by
  have he := congrArg Prod.fst (activationConsistent_trial a w h)
  simpa only [runPrefix_lift] using he.trans (by
    unfold trialDecision
    cases (runPrefix (activationRun a) w h).1 with
    | ok out => rfl
    | error e => cases e <;> rfl)

private theorem trialFilterAux (xs acc : List Activation) (w : World) (h : List Event) :
    (List.filterAuxM Env.Activation.consistent xs acc).run w =
      (List.filterAuxM (fun a => trialDecision a w h) xs acc).map (fun ys => (ys, w)) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.filterAuxM, StateT.run_bind, trialDecision_eq a w h]
    cases hr : trialDecision a w h <;> simp [Except.map, ih]

theorem trials_filter (xs : List Activation) (w : World) (h : List Event) :
    (xs.filterM Env.Activation.consistent).run w =
      (xs.filterM (fun a => trialDecision a w h)).map (fun ys => (ys, w)) := by
  simp only [List.filterM, StateT.run_bind, trialFilterAux xs [] w h]
  cases hr : List.filterAuxM (fun a => trialDecision a w h) xs [] <;> simp [Except.map]

/-- Certify any candidate's trial, including one rejected by a hidden Stop or
ending in another Stop. This does not assert that every candidate was evaluated. -/
theorem trials_safe (xs : List Activation) (w : World) (h : List Event)
    (hi : Inv deviceIndex initial h w) :
    ∀ a ∈ xs, Safe initial (runPrefix (activationRun a) w h).2 := by
  intro a _
  exact (activationRun_preserves a w h hi).choose_spec.2.1

theorem trials_initialized (xs : List Activation) (w : World) (h : List Event)
    (hi : Inv deviceIndex (PtrRing.init n) h w) :
    ∀ a ∈ xs, ∃ r, Initialized n (runPrefix (activationRun a) w h).2 r := by
  intro a ha
  obtain ⟨r, hr⟩ := trials_safe xs w h hi a ha
  exact ⟨r, hr.initialized⟩

end Leanux.Proofs.WG.Queues.RxRing
