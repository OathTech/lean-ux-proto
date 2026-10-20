import Leanux.Proofs.WG.Progress.CommittedReceiptSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns
open Leanux Leanux.Proofs.Logged

/-- Inspect one actual committed callback, retaining its receipt on Stop. The
real dispatch and resume factories install this same `run` callback. -/
def observeRun (origin : Origin) (activation : Activation) :
    Leanux.M (Campaign2.Product.Outcome Unit × List Receipt) := fun entry =>
  let out := runPrefix (run origin activation) entry []
  .ok ((Campaign2.Product.observeResult out.1,out.2),entry)

/-- A committed dispatch or resumption executes the native activation once and
emits exactly one receipt, with its actual entry, caller label and outcome.
This includes errors; consistency trials use the separate quiet source. -/
theorem original_activation_exact_capture (origin : Origin) (activation : Activation) :
    (do let result ← observeRun origin activation; pure result.1) =
      Campaign2.Product.inspect (Env.Activation.run activation) ∧
    Campaign2.Product.Returns (observeRun origin activation) (fun _ => True)
      (fun result entry => ∃ receipt, result.2 = [receipt] ∧
        receipt.origin = origin ∧ receipt.activation = activation ∧
        receipt.before = entry ∧ receipt.exit.erase = result.1 ∧
        SourceReceipt receipt) := by
  constructor
  · funext entry
    change Except.ok (Campaign2.Product.observeResult (runPrefix (run origin activation) entry []).1,entry) = _
    rw [run_erases]
    rfl
  · intro entry _
    let receipt : Receipt := ⟨origin,activation,Campaign2.Product.snapshot entry,
      (activationExitRun activation entry).map Campaign2.Product.snapshot⟩
    have same := congrArg (fun action : Leanux.M _ => action.run entry)
      (observedActivationExit_source activation)
    change Except.ok (receipt.exit.erase,entry) =
      Except.ok (Campaign2.Product.observeResult ((Env.Activation.run activation).run entry),entry) at same
    refine ⟨_,entry,rfl,receipt,?_,rfl,rfl,rfl,?_,?_⟩
    · change (runPrefix (run origin activation) entry []).2 = [receipt]
      rw [run_exact]
      rfl
    · change receipt.exit.erase = Campaign2.Product.observeResult (runPrefix (run origin activation) entry []).1
      rw [run_erases]
      exact congrArg Prod.fst (Except.ok.inj same)
    · exact ⟨entry,rfl,rfl⟩

end Leanux.Proofs.WG.Progress.CommittedRuns
