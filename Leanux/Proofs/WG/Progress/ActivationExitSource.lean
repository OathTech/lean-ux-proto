import Leanux.Proofs.WG.Progress.ActivationExitModel
import Leanux.Proofs.WG.Progress.CookieControlSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Invoke only the original iteration and final section read. The raw states
are actual successors; none is reconstructed from an observation. -/
def activationExitLoop (original : Activation) (occupancy refills : Nat) :
    Nat → Nat → Activation → World → ActivationExitResult World
  | 0, count, active, before => .exhausted count active before (.invariant
      s!"{original.worker.symbol} consumed more items than its queue held ({occupancy}) plus the refills its run could take ({refills})")
  | fuel + 1, count, active, before =>
    match (Activation.iter active).run before with
    | .error error => .iterationError count active before error
    | .ok (.ended, after) => .ended count active before after
        ((hidden (.sectionStop active.worker) : Leanux.M (List UInt8)).run after)
    | .ok (.yielded, after) => .yielded count active before after
        {after with ambient := {after.ambient with suspended := after.ambient.suspended ++
          [{active with iterations := active.iterations + 1}]}}
    | .ok (.continued, after) => activationExitLoop original occupancy refills fuel (count + 1)
        {active with iterations := active.iterations + 1} after

def activationExitRun (a : Activation) (initial : World) : ActivationExitAudit World :=
  match (Activation.occupancy a).run initial with
  | .error error => .occupancyError error
  | .ok (occupancy, afterOccupancy) =>
    match Activation.refills.run afterOccupancy with
    | .error error => .refillsError occupancy afterOccupancy error
    | .ok (refills, entry) => .ran occupancy refills entry
        (activationExitLoop a occupancy refills (occupancy + refills + 1) 0 a entry)

/-- Inspect the complete actual run. The external state remains at entry;
the operation's actual final state, or its first Stop, is in the datum. -/
def observedActivationExit (a : Activation) : Leanux.M (ActivationExitAudit Campaign2.Product.Snapshot) :=
  fun initial => .ok ((activationExitRun a initial).map Campaign2.Product.snapshot, initial)

/-- The retained exit cut comes from the actual final attempted iteration and
its real section-stop call; an exhausted loop never invents an extra poll. -/
def ActivationExitSourceFacts : ActivationExitResult World → Prop
  | .iterationError _ active before error => (Activation.iter active).run before = .error error
  | .ended _ active before middle stop =>
      (Activation.iter active).run before = .ok (.ended, middle) ∧
      (hidden (.sectionStop active.worker) : Leanux.M (List UInt8)).run middle = stop
  | .yielded _ active before middle final =>
      (Activation.iter active).run before = .ok (.yielded, middle) ∧
      final = {middle with ambient := {middle.ambient with suspended :=
        middle.ambient.suspended ++ [{active with iterations := active.iterations + 1}]}}
  | .exhausted .. => True

theorem activationExitLoop_source_facts (original : Activation) (occupancy refills fuel count : Nat)
    (active : Activation) (entry : World) :
    ActivationExitSourceFacts (activationExitLoop original occupancy refills fuel count active entry) := by
  induction fuel generalizing count active entry with
  | zero => trivial
  | succ fuel ih =>
    unfold activationExitLoop
    cases run : (Activation.iter active).run entry with
    | error error => exact run
    | ok pair =>
      obtain ⟨result, after⟩ := pair
      cases result with
      | ended => exact ⟨run, rfl⟩
      | yielded => exact ⟨run, rfl⟩
      | continued => exact ih (count + 1) _ after

/-- Both captured values and each failed read refer to the same native run.
The last-phase facts start at the real state after the second read. -/
theorem activationExitRun_source_facts (a : Activation) (initial : World) :
    match activationExitRun a initial with
    | .occupancyError error => (Activation.occupancy a).run initial = .error error
    | .refillsError occupancy afterOccupancy error =>
        (Activation.occupancy a).run initial = .ok (occupancy, afterOccupancy) ∧
        Activation.refills.run afterOccupancy = .error error
    | .ran occupancy refills entry result =>
        (∃ afterOccupancy,
          (Activation.occupancy a).run initial = .ok (occupancy, afterOccupancy) ∧
          Activation.refills.run afterOccupancy = .ok (refills, entry)) ∧
        ActivationExitSourceFacts result := by
  unfold activationExitRun
  cases read : (Activation.occupancy a).run initial with
  | error error => rfl
  | ok pair =>
    obtain ⟨occupancy, afterOccupancy⟩ := pair
    dsimp only
    cases refillRead : Activation.refills.run afterOccupancy with
    | error error => exact ⟨rfl, refillRead⟩
    | ok pair =>
      obtain ⟨refills, entry⟩ := pair
      exact ⟨⟨afterOccupancy, rfl, refillRead⟩,
        activationExitLoop_source_facts a occupancy refills (occupancy + refills + 1) 0 a entry⟩

theorem activationExitLoop_erases (original : Activation) (occupancy refills fuel start count : Nat)
    (active : Activation) (entry : World) :
    (activationExitLoop original occupancy refills fuel count active entry).erase =
      ((do let state ← activationLoopSource (List.range' start fuel) active
           activationFinishSource original occupancy refills state).run entry) := by
  induction fuel generalizing start count active entry with
  | zero => rfl
  | succ fuel ih =>
    simp only [activationLoopSource, List.range'_succ, List.forIn_cons,
      activationStepSource, StateT.run_bind, activationExitLoop]
    cases run : (Activation.iter active).run entry with
    | error error => rfl
    | ok pair =>
      obtain ⟨result, after⟩ := pair
      cases result with
      | ended =>
        dsimp only [Bind.bind, Except.bind, StateT.bind, StateT.run, ActivationExitResult.erase]
        cases stop : (hidden (.sectionStop active.worker) : Leanux.M (List UInt8)) after with
        | error error => rfl
        | ok pair => obtain ⟨bytes, final⟩ := pair; rfl
      | yielded => rfl
      | continued => exact ih (start + 1) (count + 1) _ after

theorem activationExitRun_erases (a : Activation) (entry : World) :
    (activationExitRun a entry).erase = (Activation.run a).run entry := by
  rw [activation_run_source, StateT.run_bind]
  unfold activationExitRun
  cases read : (Activation.occupancy a).run entry with
  | error error => rfl
  | ok pair =>
    obtain ⟨occupancy, afterOccupancy⟩ := pair
    change (match Activation.refills.run afterOccupancy with
      | .error error => ActivationExitAudit.refillsError occupancy afterOccupancy error
      | .ok (refills, after) => ActivationExitAudit.ran occupancy refills after
          (activationExitLoop a occupancy refills (occupancy + refills + 1) 0 a after)).erase =
      (Activation.refills.run afterOccupancy >>= fun (refills, after) =>
        (do let state ← activationLoopSource (List.range' 0 (occupancy + refills + 1)) a
            activationFinishSource a occupancy refills state).run after)
    cases refillRead : Activation.refills.run afterOccupancy with
    | error error => rfl
    | ok pair =>
      obtain ⟨refills, after⟩ := pair
      exact activationExitLoop_erases a occupancy refills (occupancy + refills + 1) 0 0 a after

theorem activationExitLoop_facts (original : Activation) (occupancy refills fuel count : Nat)
    (active : Activation) (entry : World)
    (budget : count + fuel = occupancy + refills + 1)
    (counter : active = {original with iterations := original.iterations + count}) :
    ActivationExitFacts original (.ran occupancy refills (Campaign2.Product.snapshot entry)
      ((activationExitLoop original occupancy refills fuel count active entry).map Campaign2.Product.snapshot)) := by
  induction fuel generalizing count active entry with
  | zero =>
    simp only [activationExitLoop, ActivationExitResult.map, ActivationExitFacts,
      ActivationExitResult.attempts, ActivationExitResult.active, ActivationExitResult.continued]
    exact ⟨by omega, counter, by omega, trivial⟩
  | succ fuel ih =>
    unfold activationExitLoop
    cases run : (Activation.iter active).run entry with
    | error error =>
      simp only [ActivationExitResult.map, ActivationExitFacts, ActivationExitResult.attempts,
        ActivationExitResult.active, ActivationExitResult.continued]
      exact ⟨by omega, counter, trivial⟩
    | ok pair =>
      obtain ⟨result, after⟩ := pair
      cases result with
      | ended =>
        simp only [ActivationExitResult.map, ActivationExitFacts, ActivationExitResult.attempts,
          ActivationExitResult.active, ActivationExitResult.continued]
        exact ⟨by omega, counter, trivial⟩
      | yielded =>
        simp only [ActivationExitResult.map, ActivationExitFacts, ActivationExitResult.attempts,
          ActivationExitResult.active, ActivationExitResult.continued]
        exact ⟨by omega, counter, rfl⟩
      | continued =>
        exact ih (count + 1) _ after (by omega) (by rw [counter]; simp only [Nat.add_assoc])

theorem activationExitRun_facts (a : Activation) (entry : World) :
    ActivationExitFacts a ((activationExitRun a entry).map Campaign2.Product.snapshot) := by
  unfold activationExitRun
  cases read : (Activation.occupancy a).run entry with
  | error error => trivial
  | ok pair =>
    obtain ⟨occupancy, afterOccupancy⟩ := pair
    dsimp only
    cases refillRead : Activation.refills.run afterOccupancy with
    | error error => trivial
    | ok pair =>
      obtain ⟨refills, after⟩ := pair
      exact activationExitLoop_facts a occupancy refills (occupancy + refills + 1) 0 a after (by omega)
        (by simp only [Nat.add_zero])

/-- Inspection erases to the exact original operation, including both bound reads,
iteration, section-stop and budget errors in their original order. -/
theorem observedActivationExit_source (a : Activation) :
    (do let audit ← observedActivationExit a; pure audit.erase) =
      Campaign2.Product.inspect (Activation.run a) := by
  funext entry
  have projected (out : ActivationExitAudit World) :
      (out.map Campaign2.Product.snapshot).erase = Campaign2.Product.observeResult out.erase := by
    cases out with
    | occupancyError error => rfl
    | refillsError occupancy afterOccupancy error => rfl
    | ran occupancy refills initial result =>
      cases result with
      | iterationError n active before error => rfl
      | exhausted n active before error => rfl
      | yielded n active before middle final => rfl
      | ended count active before after stop => cases stop <;> rfl
  change Except.ok (((activationExitRun a entry).map Campaign2.Product.snapshot).erase, entry) =
    Except.ok (Campaign2.Product.observeResult ((Activation.run a).run entry), entry)
  rw [projected, activationExitRun_erases]

end Leanux.Proofs.WG.Progress
