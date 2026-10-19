import Leanux.Proofs.WG.TimerDiscipline.EpisodeJournalSyscallSource
import Leanux.Proofs.WG.Progress.CommittedInitializedSource

/-! Reuse the original initialized paired runner; no replacement interpreter or callback premise. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.EpisodeJournal
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Lifetimes
open Configuration

namespace Initialized
open Lean Leanux.Runner Std.Do

def observed (trace : Trace) (placeholders : Bool) : PrefixOuter Receipt (Json × World) :=
  RoutingJoint.executeTraceWith syscall (fun json world=>(json,world)) trace placeholders

theorem observed_valid (trace : Trace) (placeholders : Bool) :
    ValidHistory (runPrefixOuter (observed trace placeholders) []).2 := by
  have checked := (prefixOuter_wp_iff (observed trace placeholders)
    (fun h=>h=[]) (fun _ h=>ValidHistory h) (fun _ h=>ValidHistory h)).mp
    (RunnerInvariant.Normal.executeTraceWith_wp (fun h _=>ValidHistory h) ValidHistory
      (fun _ _ hi=>hi) (fun _ _ _ _ hi=>hi) syscall syscall_preserves
      trace placeholders (fun _ _ receipt member=>by cases member)) [] rfl
  cases run : runPrefixOuter (observed trace placeholders) [] with
  | mk result history =>
    cases result <;> simpa only [run] using checked

theorem observed_erases (trace : Trace) (placeholders : Bool) :
    ErasesOuter (observed trace placeholders) (sourceRunner trace placeholders) := by
  intro history
  let lower : Syscall → PrefixM Empty Int := fun c=>liftPrefix (Leanux.syscall c)
  have own := congrArg Prod.fst
    (RoutingJoint.executeTraceWith_projects (fun _ : Receipt => (none : Option Empty))
      id syscall lower (fun j w=>(j,w)) (fun j w=>(j,w))
      (fun c=>Noise.DriverTags.Initialized.empty_projection _ _ (syscall_erases c))
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


end Initialized

end Leanux.Proofs.WG.TimerDiscipline.EpisodeJournal
