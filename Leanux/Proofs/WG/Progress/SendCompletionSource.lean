import Leanux.Proofs.WG.Progress.SendCompletionModel
import Leanux.Proofs.WG.Progress.BatchDrainFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- One original loop turn. Delivery precedes a normal early return; a worker
and the actual scheduler run before a continuing turn. -/
def sendCompletionTurn (_ : Nat) (_ : Option Unit × Unit) :
    Leanux.M (ForInStep (Option Unit × Unit)) := do
  if (← getDev).sendWorkQueue.isEmpty then
    deliverSent
    return .done (some (), ())
  runOneSendWorker
  schedule
  return .yield (none, ())

/-- Exact source factor, retaining the captured record budget and every Stop. -/
theorem runSendWorkers_completion_source : runSendWorkers = (do
    if (← getWG).dev.isNone then return
    requireNoCryptWork
    modifyWG fun w => {w with queuedThisCall := []}
    let budget ← recordBudget
    let result ← forIn (List.range' 0 budget) ((none, ()) : Option Unit × Unit) sendCompletionTurn
    match result.1 with
    | some value => pure value
    | none => budgetExhausted "the send work queue") := by
  unfold runSendWorkers sendCompletionTurn
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  congr 1
  funext g
  split
  · rfl
  · congr 1
    funext checked
    congr 1
    funext cleared
    congr 1
    funext budget
    congr 1
    funext result
    cases result.1 <;> rfl

/-- A turn can report completion only after observing an empty send queue.
The actual final delivery preserves the full optional Device. -/
theorem sendCompletionTurn_completion (index : Nat) (state : Option Unit × Unit)
    (initial final : World) (result : ForInStep (Option Unit × Unit))
    (run : (sendCompletionTurn index state).run initial = .ok (result,final)) :
    match result with
    | .done value => value.1.isSome = true ∧ ∃ d, final.wg.dev = some d ∧ d.sendWorkQueue = []
    | .yield value => value = (none, ()) := by
  cases device : initial.wg.dev with
  | none =>
    have read : (liftWG getDev).run initial =
        .error (.invariant "no WireGuard device in this trace's fixture") := by
      dsimp only [liftWG,getDev,StateT.run,StateT.bind,get,getThe,MonadStateOf.get,
        StateT.get,Bind.bind,Except.bind,Pure.pure,StateT.pure,Except.pure]
      rw [device]
      rfl
    change ((liftWG getDev).run initial >>= _) = _ at run
    rw [read] at run
    cases run
  | some d =>
    have read : (liftWG getDev).run initial = .ok (d,initial) := by
      dsimp only [liftWG,getDev,StateT.run,StateT.bind,get,getThe,MonadStateOf.get,
        StateT.get,Bind.bind,Except.bind,Pure.pure,StateT.pure,Except.pure]
      rw [device]
      rfl
    change ((liftWG getDev).run initial >>= _) = _ at run
    rw [read] at run
    change ((do
      if d.sendWorkQueue.isEmpty then
        deliverSent
        return .done (some (), ())
      runOneSendWorker
      schedule
      return .yield (none, ()) : Leanux.M (ForInStep (Option Unit × Unit))).run initial) = _ at run
    cases empty : d.sendWorkQueue.isEmpty with
    | true =>
      simp only [empty,ite_true,StateT.run_bind] at run
      cases delivery : deliverSent.run initial with
      | error stop => rw [delivery] at run; cases run
      | ok pair =>
        obtain ⟨ignored,afterDelivery⟩ := pair
        rw [delivery] at run
        cases run
        have same := deliverSent_sameKernel_device_variant (some d)
          initial ignored afterDelivery device delivery
        exact ⟨rfl,d,same,List.isEmpty_iff.mp empty⟩
    | false =>
      simp only [empty,Bool.false_eq_true,ite_false,StateT.run_bind] at run
      cases worker : runOneSendWorker.run initial with
      | error stop => rw [worker] at run; cases run
      | ok pair =>
        obtain ⟨ignored,middle⟩ := pair
        rw [worker] at run
        change ((schedule none).run middle >>= _) = _ at run
        cases scheduled : (schedule none).run middle with
        | error stop => rw [scheduled] at run; cases run
        | ok pair => rw [scheduled] at run; cases run; rfl

/-- A completed finite loop has an actually empty send queue; exhaustion is
not recast as completion. No invariant is assumed of intervening worker calls. -/
theorem sendCompletionLoop_done (indices : List Nat) (initial final : World)
    (result : Option Unit × Unit)
    (run : (forIn indices ((none, ()) : Option Unit × Unit) sendCompletionTurn).run initial =
      .ok (result,final)) (completed : result.1.isSome = true) :
    ∃ d, final.wg.dev = some d ∧ d.sendWorkQueue = [] := by
  induction indices generalizing initial result final with
  | nil => cases run; cases completed
  | cons index indices ih =>
    rw [List.forIn_cons,StateT.run_bind] at run
    cases turn : (sendCompletionTurn index (none, ())).run initial with
    | error stop => rw [turn] at run; cases run
    | ok pair =>
      obtain ⟨step,middle⟩ := pair
      rw [turn] at run
      cases step with
      | done value =>
        cases run
        exact (sendCompletionTurn_completion index (none, ()) initial middle (.done result) turn).2
      | yield value =>
        have valueNone : value = (none, ()) :=
          sendCompletionTurn_completion index (none, ()) initial middle (.yield value) turn
        subst value
        exact ih middle final result run completed

end Leanux.Proofs.WG.Progress
