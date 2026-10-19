import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerCompanionFrames
import Leanux.Proofs.WG.Queues.JointRunnerProjection

/-! Keeping the normal endpoint for initialization does not change the
original causal journal, including the journal returned at an indexed Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Queues
open TransmitSecurity CausalJournal

theorem history_correspondence (trace : Trace) (placeholders : Bool) (h : List Event) :
    runPrefixOuter (CausalJournal.execute trace placeholders) h =
      ((runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
        (fun j w => (j,w)) trace placeholders) h).1.map Prod.fst,
       (runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
        (fun j w => (j,w)) trace placeholders) h).2) := by
  have self (c : Syscall) : ProjectsPrefix some id
      (Driver.syscallObserved hooks c) (Driver.syscallObserved hooks c) := by
    intro w h
    simp only [List.filterMap_some]
    cases actual : runPrefix (Driver.syscallObserved hooks c) w h with
    | mk result journal => cases result <;> rfl
  have proof := RoutingJoint.executeTraceWith_projects some Prod.fst
    (Driver.syscallObserved hooks) (Driver.syscallObserved hooks)
    (fun j w => (j,w)) (fun j _ => j) self (fun _ _ => rfl) trace placeholders h
  simpa only [List.filterMap_some,CausalJournal.execute,Driver.executeObserved,
    RoutingJoint.executeTrace_rx_factor] using proof

theorem history_same (trace : Trace) (placeholders : Bool) (h : List Event) :
    (runPrefixOuter (CausalJournal.execute trace placeholders) h).2 =
    (runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun j w => (j,w)) trace placeholders) h).2 :=
  congrArg Prod.snd (history_correspondence trace placeholders h)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
