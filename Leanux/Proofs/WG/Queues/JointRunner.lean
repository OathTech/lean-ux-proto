import Leanux.Proofs.WG.Queues.JointRunnerProjection
import Leanux.Proofs.WG.Queues.JointSyscalls

/-! The routing completion and RX histories of one actual initialized runner
execution. Projections preserve every input history and indexed Stop. No routing,
identity, allocation or credit invariant is an input to this correspondence. -/
namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Lean Leanux Leanux.Runner Leanux.Proofs.Logged Configuration

def runnerTail (trace : Trace) (w : World) : PrefixOuter Event (Json × World) :=
  runnerTailWith syscall (fun j v => (j,v)) trace w

theorem runnerTail_routing (trace : Trace) (w : World) :
    ProjectsOuter routingEvent id (runnerTail trace w) (runnerTailObserved trace w) := by
  rw [runnerTail_routing_factor]
  exact runnerTailWith_projects routingEvent id syscall syscallObserved
    (fun j v => (j,v)) (fun j v => (j,v)) syscall_routing (fun _ _ => rfl) trace w

theorem runnerTail_rx (trace : Trace) (w : World) :
    ProjectsOuter rxEvent Prod.fst (runnerTail trace w) (RxHistory.runnerTail RxHistory.syscall trace w) := by
  rw [runnerTail_rx_factor]
  exact runnerTailWith_projects rxEvent Prod.fst syscall RxHistory.syscall
    (fun j v => (j,v)) (fun j _ => j) syscall_rx (fun _ _ => rfl) trace w

theorem runnerTail_erases (trace : Trace) (w : World) :
    ErasesOuter (runnerTail trace w) (sourceRunnerTail trace w) := by
  intro h
  have hp := congrArg Prod.fst (runnerTail_routing trace w h)
  have he := runnerTailObserved_erases trace w (h.filterMap routingEvent)
  have same := hp.symm.trans he
  cases hr : (runPrefixOuter (runnerTail trace w) h).1 <;>
    simpa only [hr,Except.map,id_eq] using same

def executeTrace (trace : Trace) (placeholders : Bool := false) :
    PrefixOuter Event (Json × World) :=
  executeTraceWith syscall (fun j v => (j,v)) trace placeholders

theorem executeTrace_routing (trace : Trace) (placeholders : Bool) :
    ProjectsOuter routingEvent id (executeTrace trace placeholders)
      (executeTraceObserved trace placeholders) := by
  rw [executeTrace_routing_factor]
  exact executeTraceWith_projects routingEvent id syscall syscallObserved
    (fun j v => (j,v)) (fun j v => (j,v)) syscall_routing (fun _ _ => rfl) trace placeholders

theorem executeTrace_rx (trace : Trace) (placeholders : Bool) :
    ProjectsOuter rxEvent Prod.fst (executeTrace trace placeholders)
      (RxHistory.executeTraceHistory trace placeholders) := by
  change ProjectsOuter rxEvent Prod.fst _ (RxHistory.executeTraceWith _ _ _)
  rw [executeTrace_rx_factor]
  exact executeTraceWith_projects rxEvent Prod.fst syscall RxHistory.syscall
    (fun j v => (j,v)) (fun j _ => j) syscall_rx (fun _ _ => rfl) trace placeholders

theorem executeTrace_erases (trace : Trace) (placeholders : Bool) :
    ErasesOuter (executeTrace trace placeholders) (sourceRunner trace placeholders) := by
  intro h
  have hp := congrArg Prod.fst (executeTrace_routing trace placeholders h)
  have he := executeTraceObserved_erases trace placeholders (h.filterMap routingEvent)
  have same := hp.symm.trans he
  cases hr : (runPrefixOuter (executeTrace trace placeholders) h).1 <;>
    simpa only [hr,Except.map,id_eq] using same

/-- The public JSON outcome, including its exact indexed error, is unchanged. -/
theorem executeTrace_json (trace : Trace) (placeholders : Bool) (h : List Event) :
    (runPrefixOuter (executeTrace trace placeholders) h).1.map Prod.fst =
      Runner.executeTrace trace placeholders := by
  rw [executeTrace_erases trace placeholders h]
  exact sourceRunner_json trace placeholders

end Leanux.Proofs.WG.Queues.RoutingJoint
