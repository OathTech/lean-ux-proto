import Leanux.Proofs.WG.Progress.AdvanceWaitSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Recorded normal completion gives a real receipt and the final wheel
guard at its pass bound, which can differ from the stored end read. -/
theorem observedAfterAdvance_recorded_checks :
    Campaign2.Product.Ensures observedAfterAdvance
      (fun s => s.ambient.hidden.isSome = true)
      (fun result s => ∃ receipt, result = some receipt ∧
        s.wg.jiffiesLast = some receipt.jEnd ∧ NoTimerDue receipt.pass s) := by
  intro initial result final recorded run
  unfold observedAfterAdvance at run
  rw [StateT.run_bind] at run
  cases preRun : afterAdvancePrefix.run initial with
  | error stop => rw [preRun] at run; cases run
  | ok pair =>
    obtain ⟨candidate,atPass⟩ := pair
    obtain ⟨receipt,rfl,_,_,_⟩ :=
      afterAdvancePrefix_recorded_provenance initial atPass candidate recorded preRun
    rw [preRun] at run
    change ((afterAdvanceSuffix (some receipt)).run atPass >>= _) = _ at run
    cases suffix : (afterAdvanceSuffix (some receipt)).run atPass with
    | error stop => rw [suffix] at run; cases run
    | ok pair =>
      obtain ⟨value,after⟩ := pair
      rw [suffix] at run
      cases run
      unfold afterAdvanceSuffix at suffix
      rw [StateT.run_bind] at suffix
      cases turns : (discard (runTimers receipt.pass)).run atPass with
      | error stop => rw [turns] at suffix; cases suffix
      | ok pair =>
        obtain ⟨fired,beforeFinish⟩ := pair
        rw [turns] at suffix
        exact ⟨receipt,rfl,
          timerWaitFinish_checks receipt.pass receipt.jEnd beforeFinish value final True.intro suffix⟩
end Leanux.Proofs.WG.Progress
