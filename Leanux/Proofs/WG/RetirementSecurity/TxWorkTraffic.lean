import Leanux.Proofs.WG.RetirementSecurity.TxWorkTrafficLeaves

/-! Native injection, batch and flood preserve actual pending TX service
through inline receive polls and the recorded deferred scheduler. These are
normal endpoint facts; stopped terminal histories remain a separate claim. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem inject_actor (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Preserves (At (Covered locals crypt) crypt []) (Env.inject family port msg tos ll dest) := by
  unfold Env.inject
  repeat' first
    | (rx_retention_head Env.runCryptWorkers; exact crypt_workers_actor)
    | actor_traffic_step

theorem after_batch_actor : Preserves (At (Covered locals crypt) crypt []) Env.afterBatch := by
  unfold Env.afterBatch
  repeat' first
    | (rx_retention_head Env.runCryptWorkers; exact crypt_workers_actor)
    | (rx_retention_head Env.runSendWorkers; exact send_workers_actor)
    | actor_traffic_step

theorem batch_actor (items : List Env.BatchItem) :
    Preserves (At (Covered locals crypt) crypt []) (Env.batch items) := by
  unfold Env.batch
  repeat' first
    | (rx_retention_head Env.afterBatch; exact after_batch_actor)
    | actor_traffic_step

theorem flood_actor (count port family : Nat) (messages : List (List UInt8)) :
    Preserves (At (Covered locals crypt) crypt []) (Env.flood count port family messages) := by
  unfold Env.flood
  repeat' first
    | (rx_retention_head Env.afterBatch; exact after_batch_actor)
    | actor_traffic_step

theorem observe_actor : Preserves (At (Covered locals crypt) crypt []) Env.observe := by
  unfold Env.observe
  repeat' first
    | (rx_retention_head Env.idleTimers; exact idle_timers_actor)
    | actor_traffic_step

end Leanux.Proofs.WG.RetirementSecurity.TxWork
