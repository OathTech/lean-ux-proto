import Leanux.Proofs.WG.Noise.DriverTagEnvironmentSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.LifecycleSource
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Std.Do Queues

theorem envDown_preserves (P : World → Prop)
    (frames : ∀{α : Type}(action : Leanux.M α), SameProductStore action → Preserves P action)
    (down : Preserves P (liftWG WG.wgDown))
    (idle : Preserves P Env.requireIdleDevice) :
    Preserves P Env.wgDown := by
  rw [DriverTags.Environment.envDown_factor]
  unfold DriverTags.Environment.envDownWith
  repeat' first
    | (rx_retention_head getWG; exact frames _ (fun initial=>productGetWG_spec (fun s=>s=initial)))
    | (rx_retention_head Env.requireIdleDevice; exact idle)
    | (rx_retention_head modifyRouting
       apply frames
       exact fun initial => productRouting_spec _ (fun s=>s=initial))
    | (rx_retention_head liftWG; exact down)
    | (allocation_release_lift_from WG.M; exact down)
    | (allocation_release_lift_from Net.M
       apply frames
       exact fun initial => productRouting_spec _ (fun s=>s=initial))
    | (rx_retention_head skipCut
       apply frames
       intro initial
       exact productAmbient_spec (AmbientM.skipCut _) _ (fun _ _ pre=>pre))
    | (allocation_release_lift_from AmbientM
       apply frames
       intro initial
       exact productAmbient_spec _ _ (fun _ _ pre=>pre))
    | rx_retention_step

end Leanux.Proofs.WG.Noise.LifecycleSource
