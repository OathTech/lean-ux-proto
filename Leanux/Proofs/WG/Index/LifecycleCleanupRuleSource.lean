import Leanux.Proofs.WG.Noise.PendingTimerFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.LifecycleSource
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem cleanup_preserves (P : WGWorld → Prop)
    (frames : ∀{α : Type}(action : Leanux.M α),SameProductStore action →
      Preserves (fun w : World=>P w.wg) action)
    (preexit : Preserves (fun w : World=>P w.wg) (liftWG netnsPreExit)) :
    Preserves (fun w : World=>P w.wg) Env.netnsCleanup := by
  unfold Env.netnsCleanup Env.pendingDevice
  repeat' first
    | (rx_retention_head Env.runWorker
       apply TimerDiscipline.runWorker_kernel_contract _ _
         (fun wg _ _ _=>P wg) (fun wg _ _ _=>P wg)
       change Preserves (fun w : World=>P w.wg) _)
    | (rx_retention_head getRouting
       apply frames
       apply (ProjectedAction.iff_run _ _ _).mpr
       intro w result v run
       cases run
       rfl)
    | (rx_retention_head modifyEnv
       apply frames
       apply (ProjectedAction.iff_run _ _ _).mpr
       intro w result v run
       cases run
       rfl)
    | (allocation_release_lift_from WG.M; exact preexit)
    | (allocation_release_lift_from Net.M
       apply frames
       exact fun initial=>productRouting_spec _ (fun s=>s=initial))
    | (rx_retention_head skipCut
       apply frames
       exact fun initial=>productAmbient_spec (AmbientM.skipCut _) _ (fun _ _ pre=>pre))
    | (rx_retention_head unsupported
       apply frames
       exact fun initial=>productAmbient_spec (AmbientM.unsupported _) _ (fun _ _ pre=>pre))
    | (rx_retention_head invariant
       apply frames
       exact fun initial=>productAmbient_spec (AmbientM.invariant _) _ (fun _ _ pre=>pre))
    | (rx_retention_head getAmbient
       apply frames
       exact fun initial=>productAmbient_spec (get : AmbientM Ambient) _ (fun _ _ pre=>pre))
    | (rx_retention_head peekUnit
       apply frames
       exact fun initial=>productAmbient_spec (AmbientM.peekUnit _) _ (fun _ _ pre=>pre))
    | (rx_retention_head resolveUnit
       apply frames
       exact fun initial=>productAmbient_spec (AmbientM.resolveUnit _ _ _) _ (fun _ _ pre=>pre))
    | (allocation_release_lift_from AmbientM
       apply frames
       exact fun initial=>productAmbient_spec _ _ (fun _ _ pre=>pre))
    | rx_retention_step

end Leanux.Proofs.WG.Noise.LifecycleSource
