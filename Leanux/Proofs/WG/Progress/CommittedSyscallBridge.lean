import Leanux.Proofs.WG.Noise.DriverTagRunnerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CommittedRuns.Syscalls
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Configuration

/-- Compare two exact source specializations through the empty event projection;
this transports outcomes only, and claims no provenance for an arbitrary log. -/
theorem empty_projects_erases {E F α : Type} (left : PrefixM E α)
    (right : PrefixM F α) (lower : PrefixM Empty α) (action : Leanux.M α)
    (hl : ProjectsPrefix (fun _ : E => (none : Option Empty)) id left lower)
    (hr : ProjectsPrefix (fun _ : F => (none : Option Empty)) id right lower)
    (he : ErasesPrefix right action) : ErasesPrefix left action := by
  intro w h
  have l:=congrArg Prod.fst (hl w h)
  have r:=congrArg Prod.fst (hr w [])
  have empty : h.filterMap (fun _ : E => (none : Option Empty)) = [] := by simp
  rw [empty] at l
  simp only [List.filterMap_nil] at r
  have identity (result : Except Stop (α × World)) :
      result.map (fun x=>(id x.1,x.2)) = result := by cases result <;> rfl
  rw [identity] at l r
  exact (l.symm.trans r).trans (he w [])


end Leanux.Proofs.WG.Progress.CommittedRuns.Syscalls
