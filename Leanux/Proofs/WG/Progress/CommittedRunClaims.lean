import Leanux.Proofs.WG.Progress.CommittedRunSource

/-! The original scheduler and the ordered projected receipts of the activation
calls it actually commits. This observes bounded execution; neither strict
record decrease nor callback termination is inferred from the journal. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns
open Leanux Leanux.Proofs.Logged

def observedSchedule (stack : Option Worker := none) :
    Leanux.M (Campaign2.Product.Outcome Unit × List Receipt) := fun entry =>
  let result := runPrefix (schedule stack) entry []
  .ok ((Campaign2.Product.observeResult result.1,result.2),entry)

theorem observedSchedule_source (stack : Option Worker) :
    (do let result ← observedSchedule stack; pure result.1) =
      Campaign2.Product.inspect (Env.schedule stack) := by
  funext entry
  change Except.ok (Campaign2.Product.observeResult (runPrefix (schedule stack) entry []).1,entry) =
    Except.ok (Campaign2.Product.observeResult ((Env.schedule stack).run entry),entry)
  rw [schedule_erases stack entry []]

theorem observedSchedule_valid (stack : Option Worker) :
    Campaign2.Product.Returns (observedSchedule stack) (fun _=>True)
      (fun result _=>ValidHistory result.2) := by
  intro entry _
  obtain ⟨_,_,valid,_⟩:=schedule_preserves stack entry [] (by intro r member; cases member)
  exact ⟨_,entry,rfl,valid⟩

theorem original_schedule_journal (stack : Option Worker) :
    (do let result ← observedSchedule stack; pure result.1) =
      Campaign2.Product.inspect (Env.schedule stack) ∧
    Campaign2.Product.Returns (observedSchedule stack) (fun _=>True)
      (fun result _=>∀ receipt∈result.2,ActivationExitFacts receipt.activation receipt.exit) :=
  ⟨observedSchedule_source stack,observedSchedule_valid stack⟩

end Leanux.Proofs.WG.Progress.CommittedRuns
