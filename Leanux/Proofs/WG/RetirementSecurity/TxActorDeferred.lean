import Leanux.Proofs.WG.RetirementSecurity.TxActorDeferredNeutral

/-! Actual deferred loops preserve covered TX service through recorded worker
and wheel order. The proofs retain suspended activations; their normal-return
contracts do not supply fairness, latency bounds or stopped terminal histories. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem crypt_workers_actor : Preserves (At (Covered locals crypt) crypt []) Env.runCryptWorkers := by
  unfold Env.runCryptWorkers
  exact preserves_bind (native_scheduler none) (fun _=>deliver_actor)

theorem send_workers_actor : Preserves (At (Covered locals crypt) crypt []) Env.runSendWorkers := by
  unfold Env.runSendWorkers
  repeat' actor_deferred_step

theorem after_xmit_actor : Preserves (At (Covered locals crypt) crypt []) Env.afterXmit := by
  unfold Env.afterXmit
  repeat' first
    | (rx_retention_head Env.runCryptWorkers; exact crypt_workers_actor)
    | (rx_retention_head Env.runSendWorkers; exact send_workers_actor)
    | actor_deferred_step

set_option maxHeartbeats 600000 in
theorem timers_actor (j : UInt64) : Preserves (At (Covered locals crypt) crypt []) (Env.runTimers j) := by
  unfold Env.runTimers
  repeat' first
    | (rx_retention_head Env.runCryptWorkers; exact crypt_workers_actor)
    | actor_deferred_step

set_option maxHeartbeats 600000 in
theorem placeholder_timers_actor (j : UInt64) :
    Preserves (At (Covered locals crypt) crypt []) (Env.runTimersPlaceholder j) := by
  unfold Env.runTimersPlaceholder
  repeat' first
    | (rx_retention_head Env.runCryptWorkers; exact crypt_workers_actor)
    | (rx_retention_head Env.runSendWorkers; exact send_workers_actor)
    | actor_deferred_step

theorem idle_timers_actor : Preserves (At (Covered locals crypt) crypt []) Env.idleTimers := by
  unfold Env.idleTimers
  simp (config := {zeta := false}) only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (rx_retention_head Env.runTimers; exact timers_actor _)
    | (rx_retention_head Env.runTimersPlaceholder; exact placeholder_timers_actor _)
    | actor_deferred_step

theorem advance_actor (ticks : Nat) : Preserves (At (Covered locals crypt) crypt active) (Env.advance ticks) := by
  unfold Env.advance
  repeat' actor_deferred_step

theorem after_advance_actor : Preserves (At (Covered locals crypt) crypt []) Env.afterAdvance := by
  unfold Env.afterAdvance
  simp (config := {zeta := false}) only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (rx_retention_head Env.runTimers; exact timers_actor _)
    | (rx_retention_head Env.runTimersPlaceholder; exact placeholder_timers_actor _)
    | actor_deferred_step

theorem deferred_actor (call : EnvDeferredCall) : Preserves (At (Covered locals crypt) crypt []) call.original := by
  cases call with
  | drained what queues=>exact drained_actor what queues
  | idleDevice=>exact idle_device_actor
  | noCrypt=>exact no_crypt_actor
  | crypt=>exact crypt_workers_actor
  | sendOne=>exact send_one_actor
  | clearOne=>exact clear_one_actor
  | sendAll=>exact send_workers_actor
  | afterXmit=>exact after_xmit_actor
  | timerWorker timer=>exact timer_worker_actor timer
  | timers j=>exact timers_actor j
  | placeholder j=>exact placeholder_timers_actor j
  | idle=>exact idle_timers_actor
  | advance ticks=>exact advance_actor ticks
  | afterAdvance=>exact after_advance_actor

end Leanux.Proofs.WG.RetirementSecurity.TxWork
