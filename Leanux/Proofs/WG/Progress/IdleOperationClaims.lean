import Leanux.Proofs.WG.Progress.IdleOperationSource
import Leanux.Proofs.WG.Progress.TimerWaitClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- A present receipt is the actual final clock and its successful wheel guard.
The recordless branch supplies no receipt or wheel conclusion. -/
theorem observedIdleTimers_checks :
    Campaign2.Product.Ensures observedIdleTimers (fun _ => True)
      (fun seen final => ∀ j, seen = some j →
        final.wg.jiffiesLast = some j ∧ NoTimerDue j final) := by
  intro initial seen final _ run
  change (idleTimers.run initial >>= fun pair =>
    .ok ((if initial.ambient.hidden.isSome then pair.2.wg.jiffiesLast else none),pair.2)) = _ at run
  cases waited : idleTimers.run initial with
  | error stop => rw [waited] at run; cases run
  | ok pair =>
    obtain ⟨value,middle⟩ := pair
    rw [waited] at run
    cases run
    cases recorded : initial.ambient.hidden.isSome with
    | false => simp
    | true =>
      obtain ⟨j,clock,due⟩ := idleTimers_recorded_nothing_due initial value middle recorded waited
      intro actual same
      change middle.wg.jiffiesLast = some j at clock
      simp only [ite_true,clock,Option.some.injEq] at same
      subst actual
      exact ⟨clock,due⟩

/-- A normal observed wait supplies a clock exactly when that actual wait
entered recorded mode; the theorem assumes no readiness or successful drain. -/
theorem observedIdleTimers_receipt_presence (recorded : Bool) :
    Campaign2.Product.Ensures observedIdleTimers
      (fun entry => entry.ambient.hidden.isSome = recorded)
      (fun seen _ => seen.isSome = recorded) := by
  intro initial seen final mode run
  change initial.ambient.hidden.isSome = recorded at mode
  change (idleTimers.run initial >>= fun pair =>
    .ok ((if initial.ambient.hidden.isSome then pair.2.wg.jiffiesLast else none),pair.2)) = _ at run
  cases waited : idleTimers.run initial with
  | error stop => rw [waited] at run; cases run
  | ok pair =>
    obtain ⟨value,middle⟩ := pair
    rw [waited] at run
    cases run
    cases present : initial.ambient.hidden.isSome with
    | false =>
      simp only [Bool.false_eq_true,ite_false,Option.isSome_none]
      exact present.symm.trans mode
    | true =>
      obtain ⟨j,clock,_⟩ := idleTimers_recorded_nothing_due initial value middle present waited
      change middle.wg.jiffiesLast = some j at clock
      simp only [ite_true,clock,Option.isSome_some]
      exact present.symm.trans mode

/-- A present receipt proves the wheel guard at this observed operation's
return. HasFinalIdleWait gives actual syscall correspondence by erasure.
No entry-mode persistence or successful-call premise is supplied. -/
theorem observedIdleWaitOperation_checks (call : Syscall) :
    Campaign2.Product.Ensures (observedIdleWaitOperation call) (fun _ => True)
      (fun out final => ∀ j, out.2 = some j →
        final.wg.jiffiesLast = some j ∧ NoTimerDue j final) := by
  intro initial result final _ run
  unfold observedIdleWaitOperation at run
  rw [StateT.run_bind] at run
  cases preRun : (idleWaitOperationPrefix call).run initial with
  | error stop => rw [preRun] at run; cases run
  | ok pair =>
    obtain ⟨ret,middle⟩ := pair
    rw [preRun] at run
    change (observedIdleTimers.run middle >>= _) = _ at run
    cases observed : observedIdleTimers.run middle with
    | error stop => rw [observed] at run; cases run
    | ok pair =>
      obtain ⟨seen,last⟩ := pair
      rw [observed] at run
      cases run
      exact observedIdleTimers_checks middle seen final True.intro observed

end Leanux.Proofs.WG.Progress
