import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointFrames

/-! Native environment atoms retain the packet projection on their actual
normal runs. Deletion's extra reference account is transported separately. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

theorem product_frame (body : Leanux.M α) (frame : SameProductStore body) :
    SameView (fun w : World=>StagedEntry.view w.wg) body :=
  frame.of_factor (fun s : ProductStore43=>StagedEntry.view {dev:=s.2.2.2.dev}) _ (fun _=>rfl)

theorem idle_frame : SameView (fun w : World=>StagedEntry.view w.wg) Env.requireIdleDevice :=
  product_frame _ (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerControlCalls.«0».Leanux.Proofs.WG.OwnerControlCalls.idle_store)

theorem inetdev_frame : SameView (fun w : World=>StagedEntry.view w.wg) Env.inetdevDestroy :=
  product_frame _ (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.inetdevDestroy_store)

theorem routing_frame (body : Net.M α) :
    SameView (fun w : World=>StagedEntry.view w.wg) (monadLift body : Leanux.M α) :=
  product_frame _ (fun initial=>productRouting_spec body (·=initial))

theorem task_frame (t : TaskRef) :
    SameView (fun w : World=>StagedEntry.view w.wg) (getTask t : Leanux.M Task) :=
  fun initial=>productFS_spec (monadLift (TaskM.getTask t) : FS.M Task) (fun w=>StagedEntry.view w.wg=initial) (fun _ _ _ _ before=>before)

theorem files_frame :
    SameView (fun w : World=>StagedEntry.view w.wg) (getFiles : Leanux.M FilesStruct) := by
  intro initial
  have taskFrame (a : TaskM Task) : Preserves (fun w : World=>StagedEntry.view w.wg=initial)
      (monadLift a : Leanux.M Task) :=
    productFS_spec (monadLift a : FS.M Task) _ (fun _ _ _ _ before=>before)
  change Preserves (fun w : World=>StagedEntry.view w.wg=initial) (getFiles : Leanux.M FilesStruct)
  routing_tx_source [getFiles,getTask] using [taskFrame]

theorem files_edit_frame (f : FilesStruct→FilesStruct) :
    SameView (fun w : World=>StagedEntry.view w.wg) (modifyFiles f : Leanux.M Unit) :=
  fun initial=>productFS_spec
    (monadLift (TaskM.modifyTask .task (fun t=>{t with files:=f t.files})) : FS.M Unit)
    (fun w=>StagedEntry.view w.wg=initial) (fun _ _ _ _ before=>before)

theorem native_history (body : Leanux.M α)
    (performed : runPrefix (liftPrefix body) w h=(.ok (value,v),last)) : last=h :=
  (congrArg Prod.snd performed).symm

theorem native_account (body : Leanux.M α)
    (frame : SameView (fun w : World=>StagedEntry.view w.wg) body)
    (before : CompleteCarrier.Accounted h ledger [] [] w.wg)
    (performed : runPrefix (liftPrefix body) w h=(.ok (value,v),last)) :
    CompleteCarrier.Accounted last ledger [] [] v.wg := by
  have history := native_history body performed
  subst last
  exact before.same_view ((ProjectedAction.iff_run _ _ _).mp frame w value v (congrArg Prod.fst performed))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
