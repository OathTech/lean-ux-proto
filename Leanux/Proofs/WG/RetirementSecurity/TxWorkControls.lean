import Leanux.Proofs.WG.RetirementSecurity.TxWorkControlFrames

/-! Native environment up/down/delete and namespace cleanup transport TX
service with the actual source routing notifiers and suspended worker records.
The deletion endpoint theorem remains separate from reset disposal accounting. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem env_up_actor : Preserves (At (Covered locals crypt) crypt active) Env.wgUp := by
  unfold Env.wgUp
  repeat' first
    | (allocation_release_lift_from WG.M; exact up_actor)
    | actor_control_step

theorem env_down_actor : Preserves (At (Covered locals crypt) crypt active) Env.wgDown := by
  unfold Env.wgDown
  repeat' first
    | (allocation_release_lift_from WG.M; exact down_actor)
    | actor_control_step

theorem inet_destroy_actor : Preserves (At (Covered locals crypt) crypt active) Env.inetdevDestroy := by
  unfold Env.inetdevDestroy
  repeat' actor_control_step

theorem env_mtu_actor (mtu : Nat) : Preserves (At (Covered locals crypt) crypt active) (Env.setMtu mtu) := by
  unfold Env.setMtu
  repeat' first
    | (allocation_release_lift_from WG.M; exact actor_mtu _)
    | (rx_retention_head Env.inetdevDestroy; exact inet_destroy_actor)
    | actor_control_step

theorem device_delete_actor (onDown onUnregister : Leanux.M Unit)
    (downRule : Preserves (At (Covered [] []) [] active) onDown)
    (unregisterRule : Preserves (At (Covered [] []) [] active) onUnregister) :
    Preserves (At (Covered [] []) [] active) (WG.wgDelete onDown onUnregister) := by
  unfold WG.wgDelete
  repeat' first
    | exact downRule
    | exact unregisterRule
    | (allocation_release_lift_from WG.M; first
        | exact down_actor
        | exact destruct_actor
        | exact actor_sleep)
    | actor_control_step

theorem env_delete_actor : Preserves (At (Covered [] []) [] active) Env.wgDelete := by
  unfold Env.wgDelete
  repeat' first
    | (rx_retention_head WG.wgDelete; apply device_delete_actor)
    | (rx_retention_head Env.inetdevDestroy; exact inet_destroy_actor)
    | actor_control_step

theorem cleanup_actor : Preserves (At (Covered locals crypt) crypt active) Env.netnsCleanup := by
  unfold Env.netnsCleanup
  repeat' first
    | (rx_retention_head Env.runWorker; apply run_worker_actor)
    | (allocation_release_lift_from WG.M; exact actor_pre_exit)
    | (allocation_release_lift_from Net.M
       apply actor_routing
       apply TxSuspension.Fib.creator_namespace
       suspension_source [] using [TxSuspension.Fib.cache_flush,TxSuspension.Fib.netdev_down,
         TxSuspension.Fib.addr_down,TxSuspension.Fib.netdev_unregister])
    | actor_control_step

end Leanux.Proofs.WG.RetirementSecurity.TxWork
