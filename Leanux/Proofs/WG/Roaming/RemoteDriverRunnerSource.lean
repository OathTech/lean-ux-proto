import Leanux.Proofs.WG.Roaming.RemoteDriverRunnerBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDriver.Runner
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Noise Lifetimes Queues Configuration Origins.HistorySupport Std.Do

theorem normal (trace : Trace) (placeholders : Bool) (result : Json) (w : World)
    (h : List Event) (run : runPrefixOuter (observed trace placeholders) []=(.ok (result,w),h)) :
    Inv emptyRemotes h w :=
  RunnerInvariant.Normal.executeTraceWith_normal (Inv emptyRemotes) Safe
    (safe emptyRemotes) (wg_store_inv emptyRemotes) Syscalls.call (Syscalls.call_preserves emptyRemotes)
    trace placeholders (initial trace) run

theorem history_safe (trace : Trace) (placeholders : Bool) : Safe (history trace placeholders) := by
  have checked := (prefixOuter_wp_iff (observed trace placeholders)
    (fun h=>h=[]) (fun out h=>Inv emptyRemotes h out.2) (fun _ h=>Safe h)).mp
    (RunnerInvariant.Normal.executeTraceWith_wp (Inv emptyRemotes) Safe (safe emptyRemotes)
      (wg_store_inv emptyRemotes) Syscalls.call (Syscalls.call_preserves emptyRemotes)
      trace placeholders (initial trace)) [] rfl
  cases run : runPrefixOuter (observed trace placeholders) [] with
  | mk out h =>
    cases out with
    | error stop => simpa only [history,run] using checked
    | ok out =>
      have good : Inv emptyRemotes h out.2 := by simpa only [run] using checked
      change Safe (history trace placeholders)
      rw [history,run]
      exact good.2

theorem observed_rx (trace : Trace) (placeholders : Bool) :
    ProjectsOuter rxEvent Prod.fst (observed trace placeholders) (RxHistory.executeTraceHistory trace placeholders) := by
  change ProjectsOuter rxEvent Prod.fst _ (RxHistory.executeTraceWith _ _ _)
  rw [RoutingJoint.executeTrace_rx_factor]
  exact RoutingJoint.executeTraceWith_projects rxEvent Prod.fst Syscalls.call RxHistory.syscall
    (fun j w=>(j,w)) (fun j _=>j) Syscalls.call_projects (fun _ _=>rfl) trace placeholders

theorem history_rx (trace : Trace) (placeholders : Bool) :
    (history trace placeholders).filterMap rxEvent = ConfirmationOrder.history trace placeholders := by
  exact (congrArg Prod.snd (observed_rx trace placeholders [])).symm

theorem erases (trace : Trace) (placeholders : Bool) :
    ErasesOuter (observed trace placeholders) (sourceRunner trace placeholders) := by
  intro h
  let lower : Syscall → PrefixM Empty Int := fun c=>liftPrefix (Leanux.syscall c)
  have own := congrArg Prod.fst
    (RoutingJoint.executeTraceWith_projects (fun _ : Event=>(none : Option Empty)) id
      Syscalls.call lower (fun j w=>(j,w)) (fun j w=>(j,w))
      (fun c=>DriverTags.Initialized.empty_projection _ _ (Syscalls.call_erases c))
      (fun _ _=>rfl) trace placeholders h)
  have shared := congrArg Prod.fst
    (RoutingJoint.executeTraceWith_projects (fun _ : RoutingJoint.Event=>(none : Option Empty)) id
      RoutingJoint.syscall lower (fun j w=>(j,w)) (fun j w=>(j,w))
      (fun c=>DriverTags.Initialized.empty_projection _ _ (RoutingJoint.syscall_erases c))
      (fun _ _=>rfl) trace placeholders [])
  have empty : h.filterMap (fun _ : Event=>(none : Option Empty))=[] := by simp
  rw [empty] at own
  simp only [List.filterMap_nil] at shared
  have same : (runPrefixOuter (observed trace placeholders) h).1 =
      (runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).1 := by
    simpa only [observed,RoutingJoint.executeTrace,Except.map_id,id_eq] using own.symm.trans shared
  exact same.trans (RoutingJoint.executeTrace_erases trace placeholders [])

end Leanux.Proofs.WG.Roaming.RemoteDriver.Runner
