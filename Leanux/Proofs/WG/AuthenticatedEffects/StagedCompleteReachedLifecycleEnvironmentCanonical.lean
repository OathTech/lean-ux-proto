import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecycleEnvironmentNativeFrames

/-! Canonical wrapper witnesses branch directly on the original option and
Boolean values. The underlying lifecycle bodies remain fully expanded. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity Driver Points
set_option maxHeartbeats 500000

noncomputable def upNotificationsShape : (enabled : Bool) → Shape (upNotifications enabled)
  | false => .pure _
  | true => .bind (.native (.quiet _ (routing_frame _))) (fun _=>
      .bind (.native (.quiet _ (routing_frame _))) (fun _=>
        .native (.quiet _ (env_edit_frame _))))

noncomputable def upFinishShape (ret : Int) : Shape (upFinish ret) :=
  .bind (.native (.quiet _ (fun _=>productAmbient_spec _ _ (fun _ _ before=>before))))
    (fun _=>.bind (upNotificationsShape (ret==0)) (fun _=>.pure ret))

noncomputable def upActiveShape : (running : Bool) → Shape (upActive running)
  | true => .pure _
  | false => .bind Points.upShape upFinishShape

noncomputable def upTailShape : (dev : Option Device) → Shape (upTail dev)
  | none => .pure _
  | some d => upActiveShape d.running

noncomputable def upShape : Shape up :=
  .marked .envUp (.bind (.native (.quiet _ (product_frame _ (fun initial=>productGetWG_spec (·=initial)))))
    (fun saved=>upTailShape saved.dev))

noncomputable def downBodyShape : Shape downBody := by
  unfold downBody
  repeat' lifecycle_environment_step

noncomputable def downActiveShape : (running : Bool) → Shape (downActive running)
  | false => .pure _
  | true => downBodyShape

noncomputable def downTailShape : (dev : Option Device) → Shape (downTail dev)
  | none => .pure _
  | some d => downActiveShape d.running

noncomputable def downShape : Shape down :=
  .marked .envDown (.bind (.native (.quiet _ (product_frame _ (fun initial=>productGetWG_spec (·=initial)))))
    (fun saved=>downTailShape saved.dev))

noncomputable def deleteTailShape : (absent : Bool) → Shape (deleteTail absent)
  | true => .pure _
  | false => .bind deletePrefixShape (fun _=>.bind destructShape (fun _=>.pure 0))

noncomputable def deleteShape : Shape delete :=
  .marked .envDelete (.bind deleteGuardsShape (fun _=>
    .bind (.native (.quiet _ (product_frame _ (fun initial=>productGetWG_spec (·=initial)))))
      (fun saved=>deleteTailShape saved.dev.isNone)))

noncomputable def originalUp : Shape (envUpObserved hooks) := (congrArg Shape up_source).mpr upShape
noncomputable def originalDown : Shape (envDownObserved hooks) := (congrArg Shape down_source).mpr downShape
noncomputable def originalDelete : Shape (envDeleteObserved hooks) := (congrArg Shape delete_source).mpr deleteShape

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment
