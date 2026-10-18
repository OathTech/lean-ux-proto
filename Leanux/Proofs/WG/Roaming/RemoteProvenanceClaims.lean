import Leanux.Proofs.WG.Roaming.RemoteDriverRunnerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteProvenance
open Lean Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged
def Occurs (trace : Runner.Trace) (placeholders : Bool) (origin : Origin) : Prop :=
  Matches trace placeholders (RemoteDriver.Runner.history trace placeholders) origin

def outcome (trace : Runner.Trace) (placeholders : Bool) :
    Except (Nat × Stop) (Json × Campaign2.Snapshot) :=
  (runPrefixOuter (RemoteDriver.Runner.observed trace placeholders) []).1.map
    (fun (j,w)=>(j,Campaign2.snapshot w.wg w.ambient))

theorem outcome_json (trace : Runner.Trace) (placeholders : Bool) :
    (outcome trace placeholders).map Prod.fst = Runner.executeTrace trace placeholders := by
  have same := congrArg (Except.map Prod.fst) (RemoteDriver.Runner.erases trace placeholders [])
  have json := Configuration.sourceRunner_json trace placeholders
  cases run : (runPrefixOuter (RemoteDriver.Runner.observed trace placeholders) []).1 <;>
    simpa only [outcome,run,Except.map] using same.trans json

theorem final_origins (trace : Runner.Trace) (placeholders : Bool) (json : Json)
    (final : Campaign2.Snapshot) (completed : outcome trace placeholders = .ok (json,final)) :
    ∀ pid remote, remoteMap final pid = some remote →
      ∃ origin : Origin, Occurs trace placeholders origin ∧ origin.Facts pid remote := by
  cases run : runPrefixOuter (RemoteDriver.Runner.observed trace placeholders) [] with
  | mk result h =>
    cases result with
    | error stop => simp only [outcome,run,Except.map] at completed; cases completed
    | ok result =>
      obtain ⟨j,w⟩ := result
      simp only [outcome,run,Except.map,Except.ok.injEq,Prod.mk.injEq] at completed
      obtain ⟨rfl,rfl⟩ := completed
      have good := RemoteDriver.Runner.normal trace placeholders j w h run
      have hist : RemoteDriver.Runner.history trace placeholders = h := by simp [RemoteDriver.Runner.history,run]
      intro pid remote present
      have found : destinationAt w.wg pid = some remote := present
      rcases covered_origins trace placeholders RemoteDriver.Runner.emptyRemotes (destinationAt w.wg) h
        (by rw [← hist]; exact RemoteDriver.Runner.history_rx trace placeholders)
        good.2 good.1 pid remote found with absent | ⟨origin,matched,facts⟩
      · cases absent
      · exact ⟨origin,by simpa only [Occurs,hist] using matched,facts⟩

end Leanux.Proofs.WG.Roaming.RemoteProvenance
