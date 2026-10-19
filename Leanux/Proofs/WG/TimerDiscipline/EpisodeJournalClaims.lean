import Leanux.Proofs.WG.TimerDiscipline.EpisodeJournalInitializedSource

/-! Exact initialized outcomes and ordered timer episode receipts, including failed invocations and earlier completed episodes before later indexed Stops. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.EpisodeJournal
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Lifetimes
namespace Initialized
open Lean Leanux.Runner
abbrev Inspection :=
  Except (Nat × Stop) (Json × Campaign2.Product.Snapshot) × List Receipt

def inspection (trace : Trace) (placeholders : Bool := false) : Inspection :=
  let result := runPrefixOuter (observed trace placeholders) []
  (result.1.map (fun (json,world)=>(json,Campaign2.Product.snapshot world)),result.2)

theorem inspection_json (trace : Trace) (placeholders : Bool) :
    (inspection trace placeholders).1.map Prod.fst = Runner.executeTrace trace placeholders := by
  dsimp only [inspection]
  rw [observed_erases trace placeholders []]
  have original := Configuration.sourceRunner_json trace placeholders
  cases result : Configuration.sourceRunner trace placeholders <;>
    simpa only [result,Except.map] using original

theorem original_initialized_episodes (trace : Trace) (placeholders : Bool) :
    (inspection trace placeholders).1.map Prod.fst = Runner.executeTrace trace placeholders ∧
    ∀ receipt ∈ (inspection trace placeholders).2, Valid receipt :=
  ⟨inspection_json trace placeholders,observed_valid trace placeholders⟩

end Initialized

def inspectDeferred (c : EnvDeferredCall) :
    Leanux.M (Campaign2.Product.Outcome c.Result × List Receipt) := fun entry =>
  let result:=runPrefix (deferred c) entry []
  .ok ((Campaign2.Product.observeResult result.1,result.2),entry)

theorem inspectDeferred_source (c : EnvDeferredCall) :
    (do let result←inspectDeferred c; pure result.1) =
      Campaign2.Product.inspect c.original := by
  funext entry
  change Except.ok (Campaign2.Product.observeResult (runPrefix (deferred c) entry []).1,entry) =
    Except.ok (Campaign2.Product.observeResult (c.original.run entry),entry)
  rw [deferred_erases c entry []]

theorem inspectDeferred_valid (c : EnvDeferredCall) :
    Campaign2.Product.Returns (inspectDeferred c) (fun _=>True)
      (fun result _=>ValidHistory result.2) := by
  intro entry _
  obtain ⟨_,_,valid,_⟩:=deferred_preserves c entry [] (by intro r member; cases member)
  exact ⟨_,entry,rfl,valid⟩

theorem original_deferred_episodes (c : EnvDeferredCall) :
    (do let result←inspectDeferred c; pure result.1) =
      Campaign2.Product.inspect c.original ∧
    Campaign2.Product.Returns (inspectDeferred c) (fun _=>True)
      (fun result _=>∀receipt∈result.2,Valid receipt) :=
  ⟨inspectDeferred_source c,inspectDeferred_valid c⟩

end Leanux.Proofs.WG.TimerDiscipline.EpisodeJournal
