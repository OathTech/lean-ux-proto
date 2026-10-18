import Leanux.Proofs.WG.Noise.PendingTimerFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.TimerProductRules
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem dispatch (P : World→Prop)
    (stored : ∀{α : Type}(action : Leanux.M α), SameProductStore action→Preserves P action)
    (timerSection : ∀worker body,Preserves P body→Preserves P (Env.runTimerSection worker body))
    (callback : ∀pid timer,Preserves P (liftWG (timerCallback pid timer)))
    (del : ∀pid timer,Preserves P (liftWG (delTimer pid timer)))
    (worker : Worker) (pid : PeerId) (timer : PeerTimer) (wheel : WheelEntry) (prior : Option UInt64) :
    Preserves P (timerDispatchUnit worker pid timer wheel prior) := by
  have ambient {α : Type}(action : AmbientM α) : Preserves P (liftAmbient action) :=
    stored _ (fun initial=>productAmbient_spec action _ (fun _ _ pre=>pre))
  unfold timerDispatchUnit
  simp (config := {zeta := false}) only [peekUnit]
  repeat' first
    | (rx_retention_head Env.runTimerSection; exact timerSection _ _ (callback _ _))
    | (allocation_release_lift_from WG.M; exact del _ _)
    | (rx_retention_head Env.timerWorker; exact stored _ (timerWorker_sameKernel _))
    | (rx_retention_head Env.requireStepComplete; exact stored _ (Noise.PendingScheduler.requireStepComplete_store _))
    | (rx_retention_head getWG; exact stored _ (fun initial=>productGetWG_spec (fun s=>s=initial)))
    | (rx_retention_head modifyWG; exact stored _ (fun initial=>productModifyWG_spec (fun s=>s=initial) _ (fun _=>rfl)))
    | (rx_retention_head throw; exact hoare_throw _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | rx_retention_step

theorem placeholder (P : World→Prop)
    (stored : ∀{α : Type}(action : Leanux.M α), SameProductStore action→Preserves P action)
    (timerSection : ∀worker body,Preserves P body→Preserves P (Env.runTimerSection worker body))
    (callback : ∀pid timer,Preserves P (liftWG (timerCallback pid timer)))
    (del : ∀pid timer,Preserves P (liftWG (delTimer pid timer)))
    (j : UInt64) : Preserves P (RxHistory.placeholderTimerPassSource j) := by
  have ambient {α : Type}(action : AmbientM α) : Preserves P (liftAmbient action) :=
    stored _ (fun initial=>productAmbient_spec action _ (fun _ _ pre=>pre))
  unfold RxHistory.placeholderTimerPassSource
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head Env.runTimerSection; exact timerSection _ _ (callback _ _))
    | (allocation_release_lift_from WG.M
       first | exact stored _ (liftWG_sameProductStore getDev getDev_sameWGStore) | exact del _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id P
       intro _ _
       change Preserves P _)
    | (rx_retention_head Env.timerWorker; exact stored _ (timerWorker_sameKernel _))
    | (rx_retention_head Env.requireStepComplete; exact stored _ (Noise.PendingScheduler.requireStepComplete_store _))
    | (rx_retention_head getWG; exact stored _ (fun initial=>productGetWG_spec (fun s=>s=initial)))
    | (rx_retention_head modifyWG; exact stored _ (fun initial=>productModifyWG_spec (fun s=>s=initial) _ (fun _=>rfl)))
    | (rx_retention_head throw; exact hoare_throw _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | rx_retention_step

end Leanux.Proofs.WG.Index.TimerProductRules
