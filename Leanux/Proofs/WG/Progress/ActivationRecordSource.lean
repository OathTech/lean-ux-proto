import Leanux.Proofs.WG.Progress.ActivationRecordFrames
import Leanux.Proofs.WG.Progress.ActivationRefillFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing
/-- Composition through the actual bounded activation. The iteration contracts
are explicit obligations; this rule alone is not whole-worker decrease. -/
theorem activationLoop_strict_of_iterations (worker : Worker)
    (iteration : ∀ a : Activation, a.worker = worker → ∀ records,
      Hoare (Activation.iter a) (fun w => w.ambient.hidden = some records)
        (fun result w => Tail records w.ambient.hidden ∧
          (result = .yielded → StrictTail records w.ambient.hidden)))
    (original : Activation) (occupancy refills fuel count : Nat) (active : Activation)
    (same : active.worker = worker) (entry after : World) (records : List HiddenRecord)
    (present : entry.ambient.hidden = some records)
    (run : (activationExitLoop original occupancy refills fuel count active entry).erase =
      .ok ((),after)) : StrictTail records after.ambient.hidden := by
  induction fuel generalizing count active entry after records with
  | zero => cases run
  | succ fuel ih =>
    unfold activationExitLoop at run
    cases step : (Activation.iter active).run entry with
    | error error => rw [step] at run; cases run
    | ok pair =>
      obtain ⟨result,middle⟩ := pair
      rw [step] at run
      have effects := (hoare_iff_run _ _ _).mp (iteration active same records)
        entry result middle present step
      cases result with
      | ended =>
        change (Except.map (fun (_, final) => ((),final))
          ((hidden (.sectionStop active.worker) : Leanux.M (List UInt8)).run middle)) =
            .ok ((),after) at run
        cases stop : (hidden (.sectionStop active.worker) : Leanux.M (List UInt8)).run middle with
        | error error => rw [stop] at run; cases run
        | ok pair =>
          obtain ⟨bytes,final⟩ := pair
          have strict := (hoare_iff_run _ _ _).mp
            (hidden_after_product_tail (.sectionStop active.worker) records)
            middle bytes final effects.1 stop
          rw [stop] at run
          cases run
          exact strict
      | yielded =>
        cases run
        exact effects.2 rfl
      | continued =>
        obtain ⟨rest,stored,prior⟩ := effects.1
        exact strict_extend prior (ih (count+1)
          {active with iterations := active.iterations+1} same middle after rest stored run)

/-- Occupancy and the actual refill bound only read state. Every normally returning actual run consumes a
record if its concrete iteration contracts preserve suffixes and consume on yield. -/
theorem activation_strict_of_iterations (worker : Worker)
    (iteration : ∀ a : Activation, a.worker = worker → ∀ records,
      Hoare (Activation.iter a) (fun w => w.ambient.hidden = some records)
        (fun result w => Tail records w.ambient.hidden ∧
          (result = .yielded → StrictTail records w.ambient.hidden)))
    (a : Activation) (same : a.worker = worker) (records : List HiddenRecord) :
    Hoare (Activation.run a) (fun w => w.ambient.hidden = some records)
      (fun _ w => StrictTail records w.ambient.hidden) := by
  apply (hoare_iff_run _ _ _).mpr
  intro entry value after present run
  cases value
  rw [← activationExitRun_erases] at run
  unfold activationExitRun at run
  cases read : (Activation.occupancy a).run entry with
  | error error => rw [read] at run; cases run
  | ok pair =>
    obtain ⟨occupancy,start⟩ := pair
    rw [read] at run
    have unchanged := (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run _ _ _).mp
      (activationOccupancy_sameKernel_hidden a) entry occupancy start read
    dsimp only at run
    cases refillRead : Activation.refills.run start with
    | error error => rw [refillRead] at run; cases run
    | ok pair =>
      obtain ⟨refills,loopEntry⟩ := pair
      rw [refillRead] at run
      have stateEq := (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run _ _ _).mp
        activationRefills_sameState start refills loopEntry refillRead
      exact activationLoop_strict_of_iterations worker iteration a occupancy refills
        (occupancy+refills+1) 0 a same loopEntry after records
        ((congrArg (fun w : World => w.ambient.hidden) stateEq).trans
          (unchanged.trans present)) run
end Leanux.Proofs.WG.Progress.RecordSuffix
