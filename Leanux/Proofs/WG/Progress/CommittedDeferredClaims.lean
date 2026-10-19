import Leanux.Proofs.WG.Progress.CommittedDeferredSource

/-! Exact original deferred outcomes and projected activation receipts. Safety
means the existing exit accounting facts, not standalone source provenance.
Earlier Stops retain completed audit receipts; no success, sufficient fuel,
record decrease or enclosing initialized-run conclusion is asserted. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Deferred
open Leanux Leanux.Proofs.Logged Lifetimes

/-- Inspect the original call once, retaining its exact outcome and the
scheduler activation receipts reached before that outcome. The inspector's
external state stays at entry; its outcome datum carries normal final state. -/
def observed (call : EnvDeferredCall) :
    Leanux.M (Campaign2.Product.Outcome call.Result × List Receipt) := fun entry =>
  let result := runPrefix (deferred call) entry []
  .ok ((Campaign2.Product.observeResult result.1,result.2),entry)

theorem observed_source (call : EnvDeferredCall) :
    (do let result←observed call; pure result.1) =
      Campaign2.Product.inspect call.original := by
  funext entry
  change Except.ok (Campaign2.Product.observeResult (runPrefix (deferred call) entry []).1,entry) =
    Except.ok (Campaign2.Product.observeResult (call.original.run entry),entry)
  rw [deferred_erases call entry []]

theorem observed_valid (call : EnvDeferredCall) :
    Campaign2.Product.Returns (observed call) (fun _=>True)
      (fun result _=>ValidHistory result.2) := by
  intro entry _
  obtain ⟨_,_,valid,_⟩:=deferred_preserves call entry [] (by intro r member; cases member)
  exact ⟨_,entry,rfl,valid⟩

theorem original_deferred_journal (call : EnvDeferredCall) :
    (do let result←observed call; pure result.1) =
      Campaign2.Product.inspect call.original ∧
    Campaign2.Product.Returns (observed call) (fun _=>True)
      (fun result _=>∀receipt∈result.2,ActivationExitFacts receipt.activation receipt.exit) :=
  ⟨observed_source call,observed_valid call⟩

end Leanux.Proofs.WG.Progress.CommittedRuns.Deferred
