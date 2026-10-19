import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveControlFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

macro "archive_driver_up_step" : tactic => `(tactic| first
  | unfold Preserves StatePrefixPreserves
  | maintenance_join_let
  | maintenance_join_use
  | maintenance_reduce
  | maintenance_reduce_match
  | (nonce_source_head Driver.stagingObserved; exact staging _)
  | (nonce_source_head Driver.keepaliveObserved; exact keepalive _)
  | (nonce_source_head socketInit; exact lift _ (socket (socketInit_sameSocket _)))
  | (nonce_source_head getPeer; exact lift _ (read_peer _))
  | (nonce_source_head getDev; exact lift _ (fun h => frame_store h _ getDev_sameWGStore))
  | (nonce_source_head modifyDev
     apply lift
     intro confirmed
     apply modify_device
     intro d; rfl)
  | (nonce_source_head branch; exact ambient _)
  | (nonce_source_head Pure.pure; exact pure _)
  | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
  | (nonce_source_head ForIn.forIn; apply loop)
  | maintenance_intro
  | (with_reducible split))

theorem open_device : Preserves (Driver.openObserved TimestampDriver.hooks) := by
  unfold Driver.openObserved
  repeat' archive_driver_up_step

theorem up_device : Preserves (Driver.upObserved TimestampDriver.hooks) := by
  unfold Driver.upObserved
  repeat' first
    | (nonce_source_head Driver.openObserved; exact open_device)
    | archive_driver_up_step

theorem env_up : ProductPreserves (Driver.envUpObserved TimestampDriver.hooks) := by
  change PrefixPreserves ProductInv History _
  have route {α : Type} (a : Net.M α) :
      ProductPreserves (liftPrefix (monadLift a : Leanux.M α)) :=
    product_store _ (fun s => productRouting_spec a (fun t => t = s))
  have edit (f : EnvWorld → EnvWorld) : ProductPreserves (liftPrefix (modifyEnv f)) :=
    product_lift _ (fun _ => by unfold modifyEnv; apply hoare_modify; exact fun _ hi => hi)
  unfold Driver.envUpObserved
  repeat' first
    | (nonce_product_head liftWGObserver; exact product_safe up_device)
    | (scheduler_preserve_at modifyEnv; exact edit _)
    | (scheduler_preserve_at liftM; exact route _)
    | (scheduler_preserve_at skipCut; exact product_ambient _)
    | archive_driver_deferred_step

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
