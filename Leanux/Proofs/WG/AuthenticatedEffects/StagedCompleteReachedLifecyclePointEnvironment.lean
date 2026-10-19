import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecyclePointEnvironmentFrames

/-! Original environment wrappers retain their guard and notification order.
The complete device lifecycle is expanded, not supplied as a child contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

elab "lifecycle_local_atom" : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  unless action.consumeMData.isFVar do Lean.throwError "not an original parameter"

macro "lifecycle_environment_step" : tactic => `(tactic| first
  | (lifecycle_observer_head upObserved; exact upShape)
  | (lifecycle_observer_head downObserved; exact downShape)
  | (lifecycle_observer_head destructObserved; exact destructShape)
  | (lifecycle_native_head Env.requireIdleDevice; exact .native (.quiet _ idle_frame))
  | (lifecycle_native_head Env.inetdevDestroy; exact .native (.quiet _ inetdev_frame))
  | (first | lifecycle_native_head skipCut | lifecycle_native_head unsupported
     exact .native (.quiet _ (fun initial=>productAmbient_spec _ _ (fun _ _ before=>before))))
  | (first | lifecycle_native_head Net.Fib.rtCacheFlush | lifecycle_native_head Net.Fib.netdevUp
           | lifecycle_native_head Net.Fib.netdevDown | lifecycle_native_head Net.Fib.netdevUnregister
           | lifecycle_native_head modifyRouting | lifecycle_native_head liftM
     exact .native (.quiet _ (routing_frame _)))
  | (lifecycle_native_head getFiles; exact .native (.quiet _ files_frame))
  | (lifecycle_native_head modifyFiles; exact .native (.quiet _ (files_edit_frame _)))
  | (lifecycle_native_head liftFS
     exact .native (.quiet _ (fun initial=>productFS_spec _ _ (fun _ _ _ _ before=>before))))
  | (lifecycle_native_head getTask
     exact .native (.quiet _ (task_frame _)))
  | lifecycle_shape_step)

noncomputable def envUpShape : Shape (envUpObserved hooks) := by
  apply Shape.marked .envUp
  unfold envUpObserved
  repeat' lifecycle_environment_step

noncomputable def envDownShape : Shape (envDownObserved hooks) := by
  apply Shape.marked .envDown
  unfold envDownObserved SendExchange.envDownWith
  repeat' lifecycle_environment_step

noncomputable def deleteGuardsShape : Shape (liftPrefix Queues.RxCredits.HolderDeviceDelete.guards) := by
  unfold Queues.RxCredits.HolderDeviceDelete.guards
  repeat' lifecycle_environment_step

noncomputable def deletePrefixShape : Shape RetiredPeer.Lifecycle.Packet.Environment.prefixObserved := by
  unfold RetiredPeer.Lifecycle.Packet.Environment.prefixObserved
    RetiredPeer.Lifecycle.Packet.Environment.notifyDown RetiredPeer.Lifecycle.Packet.Environment.notifyUnregister
  index_unfold _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.notifyDown
  index_unfold _private.Leanux.Proofs.WG.Queues.HolderDeviceDelete.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceDelete.notifyUnregister
  repeat' lifecycle_environment_step

noncomputable def envDeleteShape : Shape (envDeleteObserved hooks) := by
  apply Shape.marked .envDelete
  rw [RetiredPeer.Lifecycle.Packet.Environment.source_factor]
  apply Shape.bind deleteGuardsShape
  intro _
  apply Shape.bind (.native (.quiet _ (by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w value v run
    cases run
    rfl)))
  intro saved
  split
  · exact .pure _
  · exact .bind deletePrefixShape (fun _=>.bind destructShape (fun _=>.pure 0))

noncomputable def socketShape (fd : Nat) (body : Shape action) :
    Shape (socketCallOnWith (fun {_} a=>liftPrefix a) fd action) := by
  unfold socketCallOnWith
  apply Shape.bind (.native (.quiet _ (fun initial=>productFS_spec _ _ (fun _ _ _ _ before=>before))))
  intro f
  split
  · exact .pure _
  · exact .bind body (fun ret=>.bind (.native (.quiet _ (fun initial=>productFS_spec _ _ (fun _ _ _ _ before=>before)))) (fun _=>.pure ret))

noncomputable def rtnetlinkShape (body : Shape action) :
    Shape (rtnetlinkRequestWith (fun {_} a=>liftPrefix a) action) := by
  unfold rtnetlinkRequestWith
  repeat' first
    | (lifecycle_local_atom; exact body)
    | (lifecycle_shape_head socketCallOnWith; apply socketShape)
    | lifecycle_environment_step

noncomputable def dispatchCreateShape : Shape (dispatchCreateObserved (E:=Event)) :=
  .marked .dispatchCreate (rtnetlinkShape createShape)

noncomputable def dispatchDeleteShape : Shape (dispatchDeleteObserved hooks) :=
  .marked .dispatchDelete (rtnetlinkShape envDeleteShape)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Points
