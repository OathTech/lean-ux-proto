import Leanux.Proofs.WG.Noise.DriverTagRunnerFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Initialized
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Configuration Origins.HistorySupport Std.Do

def observed (call : Syscall → ProductObs Int) (trace : Trace) (placeholders : Bool) :
    PrefixOuter DriverTagEvent (Json × World) :=
  RoutingJoint.executeTraceWith call (fun j v => (j,v)) trace placeholders

theorem normal (call : Syscall → ProductObs Int)
    (calls : ∀ c, PrefixPreserves (StateInv emptyTags) ValidHistory (call c))
    (trace : Trace) (placeholders : Bool) (result : Json) (w : World) (h : List DriverTagEvent)
    (run : runPrefixOuter (observed call trace placeholders) [] = (.ok (result,w),h)) :
    StateInv emptyTags h w :=
  RunnerInvariant.Normal.executeTraceWith_normal (StateInv emptyTags) ValidHistory
    (safe emptyTags) (state_store emptyTags) call calls trace placeholders (initial trace) run

theorem history (call : Syscall → ProductObs Int)
    (calls : ∀ c, PrefixPreserves (StateInv emptyTags) ValidHistory (call c))
    (trace : Trace) (placeholders : Bool) :
    ValidHistory (runPrefixOuter (observed call trace placeholders) []).2 := by
  have checked := (prefixOuter_wp_iff (observed call trace placeholders)
    (fun h => h = []) (fun out h => StateInv emptyTags h out.2)
    (fun _ h => ValidHistory h)).mp
    (RunnerInvariant.Normal.executeTraceWith_wp (StateInv emptyTags) ValidHistory
      (safe emptyTags) (state_store emptyTags) call calls trace placeholders (initial trace)) [] rfl
  cases run : runPrefixOuter (observed call trace placeholders) [] with
  | mk out h =>
    cases out with
    | error stop => simpa only [run] using checked
    | ok out =>
      have good : StateInv emptyTags h out.2 := by
        simpa only [run] using checked
      exact good.2

theorem empty_projection {E α : Type} (observer : PrefixM E α) (action : Leanux.M α)
    (erases : ErasesPrefix observer action) :
    ProjectsPrefix (fun _ : E => (none : Option Empty)) id observer
      (liftPrefix action : PrefixM Empty α) := by
  intro w h
  simp only [runPrefix_lift]
  have empty (l : List E) : l.filterMap (fun _ => (none : Option Empty)) = [] := by simp
  rw [empty,empty,erases w h]
  cases action.run w <;> rfl

theorem erases (call : Syscall → ProductObs Int)
    (calls : ∀ c, ErasesPrefix (call c) (Leanux.syscall c))
    (trace : Trace) (placeholders : Bool) :
    ErasesOuter (observed call trace placeholders) (sourceRunner trace placeholders) := by
  intro h
  let lower : Syscall → PrefixM Empty Int := fun c => liftPrefix (Leanux.syscall c)
  have own := congrArg Prod.fst
    (RoutingJoint.executeTraceWith_projects (fun _ : DriverTagEvent => (none : Option Empty))
      id call lower (fun j v => (j,v)) (fun j v => (j,v))
      (fun c => empty_projection _ _ (calls c)) (fun _ _ => rfl) trace placeholders h)
  have shared := congrArg Prod.fst
    (RoutingJoint.executeTraceWith_projects (fun _ : RoutingJoint.Event => (none : Option Empty))
      id RoutingJoint.syscall lower (fun j v => (j,v)) (fun j v => (j,v))
      (fun c => empty_projection _ _ (RoutingJoint.syscall_erases c))
      (fun _ _ => rfl) trace placeholders [])
  have emptyHistory : h.filterMap (fun _ : DriverTagEvent => (none : Option Empty)) = [] := by simp
  rw [emptyHistory] at own
  simp only [List.filterMap_nil] at shared
  have same : (runPrefixOuter (observed call trace placeholders) h).1 =
      (runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).1 := by
    simpa only [observed,RoutingJoint.executeTrace,Except.map_id,id_eq] using own.symm.trans shared
  exact same.trans (RoutingJoint.executeTrace_erases trace placeholders [])


theorem json (call : Syscall → ProductObs Int)
    (calls : ∀ c, ErasesPrefix (call c) (Leanux.syscall c))
    (trace : Trace) (placeholders : Bool) (h : List DriverTagEvent) :
    (runPrefixOuter (observed call trace placeholders) h).1.map Prod.fst =
      Runner.executeTrace trace placeholders := by
  rw [erases call calls trace placeholders h]
  exact sourceRunner_json trace placeholders


end Leanux.Proofs.WG.Noise.DriverTags.Initialized
