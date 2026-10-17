import Leanux.Proofs.WG.Queues.RoutingDispatchFrame
import Leanux.Proofs.WG.Queues.RxTrafficAppends

/-! All syscall constructors use one joint execution. Set and deletion keep
completed routing mutations; all other arms focus their actual RX observer.
No invariant, initialization, successful outcome or empty history is assumed. -/
namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Configuration

def dispatch : Syscall → PrefixM Event Int
  | .wgSet attrs => dispatchSet attrs
  | .wgCreate => dispatchCreate
  | .wgDelete => dispatchDelete
  | call => rxAction (RxHistory.syscallDispatch call)

theorem dispatch_routing (call : Syscall) :
    ProjectsPrefix routingEvent id (dispatch call) (dispatchObserved call) := by
  cases call
  case wgSet attrs => exact dispatchSet_routing attrs
  case wgCreate => exact dispatchCreate_routing
  case wgDelete => exact dispatchDelete_routing
  all_goals
    rw [dispatchObserved_eq_lift _ (by intro attrs h; cases h) (by intro h; cases h)]
    exact rxAction_routing (RxHistory.syscallDispatch_erases _)

theorem dispatch_rx (call : Syscall) :
    ProjectsPrefix rxEvent id (dispatch call) (RxHistory.syscallDispatch call) := by
  cases call
  case wgSet attrs => exact dispatchSet_rx attrs
  case wgCreate => exact dispatchCreate_rx
  case wgDelete => exact dispatchDelete_rx
  all_goals exact rxAction_rx (RxHistory.syscallDispatch_appends _)

theorem dispatch_erases (call : Syscall) : ErasesPrefix (dispatch call) (Leanux.dispatch call) := by
  intro w h
  have hp := congrArg Prod.fst (dispatch_rx call w h)
  have he := RxHistory.syscallDispatch_erases call w (h.filterMap rxEvent)
  have same := hp.symm.trans he
  change ((runPrefix (dispatch call) w h).1.map (fun (x,v) => (x,v))) = _ at same
  cases hr : (runPrefix (dispatch call) w h).1 <;> simpa only [hr,Except.map] using same

def syscall (call : Syscall) : PrefixM Event Int :=
  syscallWith (fun {_} a => liftPrefix a) (dispatch call)
    (rxAction RxHistory.runSendWorkers) (rxAction RxHistory.idleTimers)
    (rxAction (RxHistory.audit routeIntoWg0Audit)) (rxAction RxHistory.afterXmit)
    (rxAction RxHistory.afterAdvance) (rxAction (RxHistory.audit envNetnsCleanupAudit)) call

theorem syscall_routing (call : Syscall) :
    ProjectsPrefix routingEvent id (syscall call) (syscallObserved call) := by
  rw [syscallObserved_factor]
  exact syscallWith_projects routingEvent (dispatch_routing call)
    (rxAction_routing RxHistory.runSendWorkers_erases) (rxAction_routing RxHistory.idleTimers_erases)
    (rxAction_routing (RxHistory.audit_erases routeIntoWg0Audit_erases))
    (rxAction_routing RxHistory.afterXmit_erases) (rxAction_routing RxHistory.afterAdvance_erases)
    (rxAction_routing (RxHistory.audit_erases envNetnsCleanupAudit_erases)) call

theorem syscall_rx (call : Syscall) :
    ProjectsPrefix rxEvent id (syscall call) (RxHistory.syscall call) := by
  rw [syscallRx_factor]
  exact syscallWith_projects rxEvent (dispatch_rx call)
    (rxAction_rx RxHistory.runSendWorkers_appends) (rxAction_rx RxHistory.idleTimers_appends)
    (rxAction_rx (Appends.focus _ _ _)) (rxAction_rx RxHistory.afterXmit_appends)
    (rxAction_rx RxHistory.afterAdvance_appends) (rxAction_rx (Appends.focus _ _ _)) call

theorem syscall_erases (call : Syscall) : ErasesPrefix (syscall call) (Leanux.syscall call) := by
  intro w h
  have hp := congrArg Prod.fst (syscall_rx call w h)
  have he := RxHistory.syscall_erases call w (h.filterMap rxEvent)
  have same := hp.symm.trans he
  change ((runPrefix (syscall call) w h).1.map (fun (x,v) => (x,v))) = _ at same
  cases hr : (runPrefix (syscall call) w h).1 <;> simpa only [hr,Except.map] using same

end Leanux.Proofs.WG.Queues.RoutingJoint
