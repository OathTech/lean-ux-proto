import Leanux.Proofs.WG.Index.LifecycleEnvironmentRuleSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.LifecycleSource
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Std.Do Queues

theorem envDelete_preserves (P : WGWorld → Prop)
    (frames : ∀{α : Type}(action : Leanux.M α),SameProductStore action →
      Preserves (fun w : World=>P w.wg) action)
    (down : Preserves (fun w : World=>P w.wg) (liftWG WG.wgDown))
    (destruct : Preserves (fun w : World=>P w.wg) (liftWG wgDestruct)) :
    Preserves (fun w : World=>P w.wg) Env.wgDelete := by
  rw [Configuration.envDelete_factor]
  unfold Configuration.envDeleteWith
  repeat' first
    | (rx_retention_head getWG; exact frames _
        (fun initial => productGetWG_spec (fun s=>s=initial)))
    | (rx_retention_head Env.requireIdleDevice; exact frames _ PendingScheduler.requireIdleDevice_store)
    | (rx_retention_head liftWG
       first
       | exact down
       | exact destruct
       | exact frames _ (liftWG_sameProductStore _ getDev_sameWGStore)
       | exact frames _ (liftWG_sameProductStore _ mayHaveSlept_sameWGStore))
    | (allocation_release_lift_from Net.M; exact frames _
        (fun initial => productRouting_spec _ (fun s=>s=initial)))
    | (rx_retention_head Env.inetdevDestroy; exact frames _ DriverTags.Environment.inetdev_store)
    | (rx_retention_head modifyRouting; exact frames _
        (fun initial => productRouting_spec _ (fun s=>s=initial)))
    | (rx_retention_head unsupported; exact productAmbient_spec (AmbientM.unsupported _) _ (fun _ _ pre=>pre))
    | (rx_retention_head skipCut; exact productAmbient_spec (AmbientM.skipCut _) _ (fun _ _ pre=>pre))
    | (allocation_release_lift_from AmbientM; exact productAmbient_spec _ _ (fun _ _ pre=>pre))
    | rx_retention_step

end Leanux.Proofs.WG.Noise.LifecycleSource
