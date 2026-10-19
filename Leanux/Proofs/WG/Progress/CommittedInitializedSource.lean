import Leanux.Proofs.WG.Progress.CommittedSyscallSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Initialized
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Lifetimes Queues Configuration Std.Do

/-- The existing initialized paired runner, with the actual syscall observer
installed once. Initialization and final runner checks retain their own Stops. -/
def observed (trace : Trace) (placeholders : Bool) :
    PrefixOuter Receipt (Json × World) :=
  RoutingJoint.executeTraceWith Syscalls.syscall (fun json world=>(json,world)) trace placeholders

namespace History

theorem observed_valid (S : List Receipt → Prop)
    (runs : ∀ origin activation, PrefixPreserves (fun h _=>S h) S (run origin activation)) (empty : S []) (trace : Trace) (placeholders : Bool) :
    S (runPrefixOuter (observed trace placeholders) []).2 := by
  have checked := (prefixOuter_wp_iff (observed trace placeholders)
    (fun h=>h=[]) (fun _ h=>S h) (fun _ h=>S h)).mp
    (RunnerInvariant.Normal.executeTraceWith_wp (fun h _=>S h) S
      (fun _ _ hi=>hi) (fun _ _ _ _ hi=>hi) Syscalls.syscall (Leanux.Proofs.WG.Progress.CommittedRuns.Syscalls.History.syscall_preserves S runs)
      trace placeholders (fun _ _=>empty)) [] rfl
  cases run : runPrefixOuter (observed trace placeholders) [] with
  | mk result history =>
    cases result <;> simpa only [run] using checked

end History

theorem observed_valid (trace : Trace) (placeholders : Bool) :
    ValidHistory (runPrefixOuter (observed trace placeholders) []).2 :=
  History.observed_valid ValidHistory CommittedRuns.run_preserves (by intro receipt member; cases member) trace placeholders

theorem observed_erases (trace : Trace) (placeholders : Bool) :
    ErasesOuter (observed trace placeholders) (sourceRunner trace placeholders) := by
  intro history
  let lower : Syscall → PrefixM Empty Int := fun c=>liftPrefix (Leanux.syscall c)
  have own := congrArg Prod.fst
    (RoutingJoint.executeTraceWith_projects (fun _ : Receipt => (none : Option Empty))
      id Syscalls.syscall lower (fun j w=>(j,w)) (fun j w=>(j,w))
      (fun c=>Noise.DriverTags.Initialized.empty_projection _ _ (Syscalls.syscall_erases c))
      (fun _ _=>rfl) trace placeholders history)
  have shared := congrArg Prod.fst
    (RoutingJoint.executeTraceWith_projects (fun _ : RoutingJoint.Event => (none : Option Empty))
      id RoutingJoint.syscall lower (fun j w=>(j,w)) (fun j w=>(j,w))
      (fun c=>Noise.DriverTags.Initialized.empty_projection _ _ (RoutingJoint.syscall_erases c))
      (fun _ _=>rfl) trace placeholders [])
  have empty : history.filterMap (fun _ : Receipt => (none : Option Empty)) = [] := by simp
  rw [empty] at own
  simp only [List.filterMap_nil] at shared
  have same : (runPrefixOuter (observed trace placeholders) history).1 =
      (runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).1 := by
    simpa only [observed,RoutingJoint.executeTrace,Except.map_id,id_eq] using own.symm.trans shared
  exact same.trans (RoutingJoint.executeTrace_erases trace placeholders [])

end Leanux.Proofs.WG.Progress.CommittedRuns.Initialized
