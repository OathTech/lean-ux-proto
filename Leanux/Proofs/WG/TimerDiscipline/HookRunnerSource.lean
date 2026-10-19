import Leanux.Proofs.WG.Progress.CommittedInitializedSource
/-! Generic initialized execution of an observed syscall. This instantiates the
existing paired runner and hides its native state in projected claims. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookRunner
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Lifetimes Queues Configuration Std.Do
variable {E : Type}

def observed (syscall : Syscall → PrefixM E Int) (trace : Trace) (placeholders : Bool) :
    PrefixOuter E (Json × World) :=
  RoutingJoint.executeTraceWith syscall (fun json world=>(json,world)) trace placeholders

theorem observed_preserves (syscall : Syscall → PrefixM E Int) (S : List E → Prop)
    (hc : ∀ c, PrefixPreserves (fun h _=>S h) S (syscall c)) (empty : S [])
    (trace : Trace) (placeholders : Bool) :
    S (runPrefixOuter (observed syscall trace placeholders) []).2 := by
  have checked := (prefixOuter_wp_iff (observed syscall trace placeholders)
    (fun h=>h=[]) (fun _ h=>S h) (fun _ h=>S h)).mp
    (RunnerInvariant.Normal.executeTraceWith_wp (fun h _=>S h) S
      (fun _ _ hi=>hi) (fun _ _ _ _ hi=>hi) syscall hc
      trace placeholders (fun _ _=>empty)) [] rfl
  cases run : runPrefixOuter (observed syscall trace placeholders) [] with
  | mk result history =>
    cases result <;> simpa only [run] using checked

theorem observed_erases (syscall : Syscall → PrefixM E Int)
    (hc : ∀ c, ErasesPrefix (syscall c) (Leanux.syscall c))
    (trace : Trace) (placeholders : Bool) :
    ErasesOuter (observed syscall trace placeholders) (sourceRunner trace placeholders) := by
  intro history
  let lower : Syscall → PrefixM Empty Int := fun c=>liftPrefix (Leanux.syscall c)
  have own := congrArg Prod.fst
    (RoutingJoint.executeTraceWith_projects (fun _ : E => (none : Option Empty))
      id syscall lower (fun j w=>(j,w)) (fun j w=>(j,w))
      (fun c=>Noise.DriverTags.Initialized.empty_projection _ _ (hc c))
      (fun _ _=>rfl) trace placeholders history)
  have shared := congrArg Prod.fst
    (RoutingJoint.executeTraceWith_projects (fun _ : RoutingJoint.Event => (none : Option Empty))
      id RoutingJoint.syscall lower (fun j w=>(j,w)) (fun j w=>(j,w))
      (fun c=>Noise.DriverTags.Initialized.empty_projection _ _ (RoutingJoint.syscall_erases c))
      (fun _ _=>rfl) trace placeholders [])
  have empty : history.filterMap (fun _ : E => (none : Option Empty)) = [] := by simp
  rw [empty] at own
  simp only [List.filterMap_nil] at shared
  have same : (runPrefixOuter (observed syscall trace placeholders) history).1 =
      (runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).1 := by
    simpa only [observed,RoutingJoint.executeTrace,Except.map_id,id_eq] using own.symm.trans shared
  exact same.trans (RoutingJoint.executeTrace_erases trace placeholders [])

end Leanux.Proofs.WG.TimerDiscipline.HookRunner
