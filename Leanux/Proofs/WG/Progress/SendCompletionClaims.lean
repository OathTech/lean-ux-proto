import Leanux.Proofs.WG.Progress.SendCompletionSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Normal return of the original loop leaves either no Device or an empty
send-work queue, for arbitrary modes, inputs and queue growth. -/
theorem runSendWorkers_completion :
    Campaign2.Product.Ensures runSendWorkers (fun _ => True)
      (fun _ final => SendWorkersComplete final) := by
  intro initial result final _ run
  rw [runSendWorkers_completion_source] at run
  change ((do
    if initial.wg.dev.isNone then return
    requireNoCryptWork
    modifyWG fun w => {w with queuedThisCall := []}
    let budget ← recordBudget
    let result ← forIn (List.range' 0 budget) ((none, ()) : Option Unit × Unit) sendCompletionTurn
    match result.1 with
    | some value => pure value
    | none => budgetExhausted "the send work queue" : Leanux.M Unit).run initial) = _ at run
  cases device : initial.wg.dev with
  | none =>
    simp only [device,Option.isNone_none,ite_true] at run
    cases run
    exact .inl device
  | some d =>
    simp only [device,Option.isNone_some,Bool.false_eq_true,ite_false,StateT.run_bind] at run
    cases required : requireNoCryptWork.run initial with
    | error stop => rw [required] at run; cases run
    | ok pair =>
      obtain ⟨ignored,middle⟩ := pair
      rw [required] at run
      let before := {middle with wg := {middle.wg with queuedThisCall := []}}
      let budget := match middle.ambient.hidden with
        | some records => records.length + 1
        | none => DOMAIN_FILTER_TURNS
      change ((forIn (List.range' 0 budget) ((none, ()) : Option Unit × Unit) sendCompletionTurn).run before >>=
        fun (state,afterLoop) => ((match state.1 with
          | some value => pure value
          | none => budgetExhausted "the send work queue" : Leanux.M Unit).run afterLoop)) = _ at run
      cases loopRun : (forIn (List.range' 0 budget) ((none, ()) : Option Unit × Unit) sendCompletionTurn).run before with
      | error stop => rw [loopRun] at run; cases run
      | ok pair =>
        obtain ⟨state,afterLoop⟩ := pair
        rw [loopRun] at run
        cases done : state.1 with
        | none =>
          change (match state.1 with
            | some value => pure value
            | none => budgetExhausted "the send work queue" : Leanux.M Unit).run afterLoop = _ at run
          rw [done] at run
          change ((AmbientM.budgetExhausted "the send work queue").run afterLoop.ambient >>= _) = _ at run
          dsimp only [AmbientM.budgetExhausted,StateT.run,StateT.bind,get,getThe,
            MonadStateOf.get,StateT.get,Bind.bind,Except.bind,Pure.pure,StateT.pure,Except.pure] at run
          cases hidden : afterLoop.ambient.hidden <;> rw [hidden] at run
          all_goals change Except.error _ = Except.ok _ at run
          all_goals cases run
        | some value =>
          change (match state.1 with
            | some value => pure value
            | none => budgetExhausted "the send work queue" : Leanux.M Unit).run afterLoop = _ at run
          rw [done] at run
          cases run
          exact .inr (sendCompletionLoop_done (List.range' 0 budget) before final state loopRun (by simp [done]))

end Leanux.Proofs.WG.Progress
