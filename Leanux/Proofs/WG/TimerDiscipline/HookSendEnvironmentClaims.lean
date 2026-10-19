import Leanux.Proofs.WG.TimerDiscipline.HookSendEnvironmentSource

/-! Actual environment selection, dequeue, section and callback inspection.
The inspected original outcome includes section-stop and final payment errors;
earlier hook receipts survive both. No scheduler-completeness claim appears. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookJournal.SendEnvironment
open Leanux Leanux.WG Leanux.Proofs.Logged

def inspection : Leanux.M (Campaign2.Product.Outcome Unit × List Receipt) := fun w =>
  let result := runPrefix one w []
  .ok ((Campaign2.Product.observeResult result.1,result.2),w)

theorem inspection_source :
    (do let result←inspection; pure result.1) =
      Campaign2.Product.inspect Env.runOneSendWorker := by
  funext w
  change Except.ok (Campaign2.Product.observeResult (runPrefix one w []).1,w) =
    Except.ok (Campaign2.Product.observeResult (Env.runOneSendWorker.run w),w)
  rw [one_erases w []]

theorem inspection_valid :
    Campaign2.Product.Returns inspection (fun _=>True)
      (fun result _=>ValidHistory result.2) := by
  intro w _
  obtain ⟨_,_,valid,_⟩:=one_preserves w [] (by intro r member; cases member)
  exact ⟨_,w,rfl,valid⟩

theorem original :
    (do let result←inspection; pure result.1) =
      Campaign2.Product.inspect Env.runOneSendWorker ∧
    Campaign2.Product.Returns inspection (fun _=>True)
      (fun result _=>∀r∈result.2,r.Valid) :=
  ⟨inspection_source,inspection_valid⟩

end Leanux.Proofs.WG.TimerDiscipline.HookJournal.SendEnvironment
