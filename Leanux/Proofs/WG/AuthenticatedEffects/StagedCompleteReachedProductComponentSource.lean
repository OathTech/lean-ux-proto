import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTrafficStoreSource

/-! Subsystem computations run on extracted component values. Their native
adapters write back only those components and Ambient; WG is retained. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductStore
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def fsBody (body : FS.M α) : Leanux.M α := do
  let w ← (get : Leanux.M World)
  let pair ← liftAmbient ((body.run w.fs).run w.tasks)
  modify fun v=>{v with fs:=pair.1.2,tasks:=pair.2}
  pure pair.1.1

theorem fs_source (body : FS.M α) : liftFS body=fsBody body := by
  funext w
  change (liftFS body).run w=(fsBody body).run w
  rw [liftFS_run]
  cases performed : (((body.run w.fs).run w.tasks).run w.ambient) <;>
    simp [fsBody,StateT.run_bind,liftAmbient_run,performed,Except.map]

def taskBody (body : TaskM α) : Leanux.M α := do
  let w ← (get : Leanux.M World)
  let pair ← liftAmbient (body.run w.tasks)
  modify fun v=>{v with tasks:=pair.2}
  pure pair.1

theorem task_source (body : TaskM α) : liftTask body=taskBody body := by
  funext w
  change (liftTask body).run w=(taskBody body).run w
  rw [liftTask_run]
  cases performed : ((body.run w.tasks).run w.ambient) <;>
    simp [taskBody,StateT.run_bind,liftAmbient_run,performed,Except.map]

def seccompBody (body : Seccomp.M α) : Leanux.M α := do
  let w ← (get : Leanux.M World)
  let pair ← liftAmbient ((body.run w.seccomp).run w.tasks)
  modify fun v=>{v with seccomp:=pair.1.2,tasks:=pair.2}
  pure pair.1.1

theorem seccomp_source (body : Seccomp.M α) : liftSeccomp body=seccompBody body := by
  funext w
  change (liftSeccomp body).run w=(seccompBody body).run w
  rw [liftSeccomp_run]
  cases performed : (((body.run w.seccomp).run w.tasks).run w.ambient) <;>
    simp [seccompBody,StateT.run_bind,liftAmbient_run,performed,Except.map]

noncomputable def fsShape (body : FS.M α) : Shape (liftFS body) := by
  rw [fs_source]
  unfold fsBody
  repeat' traffic_store_step

noncomputable def taskShape (body : TaskM α) : Shape (liftTask body) := by
  rw [task_source]
  unfold taskBody
  repeat' traffic_store_step

noncomputable def seccompShape (body : Seccomp.M α) : Shape (liftSeccomp body) := by
  rw [seccomp_source]
  unfold seccompBody
  repeat' traffic_store_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductStore
