import Leanux.Proofs.WG.Lifetimes.EnvTimersAudit

/-! Fourteen current deferred-worker, guard and timer environment calls. Their
result types and failure histories remain exact; concrete allocation contracts
also certify every consistency-filter entry observed through actual scheduling. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

inductive EnvDeferredCall where
  | drained (what : String) (queues : List Bool)
  | idleDevice
  | noCrypt
  | crypt
  | sendOne
  | clearOne
  | sendAll
  | afterXmit
  | timerWorker (timer : PeerTimer)
  | timers (jHi : UInt64)
  | placeholder (jHi : UInt64)
  | idle
  | advance (ticks : Nat)
  | afterAdvance

namespace EnvDeferredCall

def Result : EnvDeferredCall → Type
  | .timerWorker _ => Worker
  | .timers _ => Bool
  | .advance _ => Int
  | _ => Unit

def original : (call : EnvDeferredCall) → Leanux.M call.Result
  | .drained what queues => Env.requireDrained what queues
  | .idleDevice => Env.requireIdleDevice
  | .noCrypt => Env.requireNoCryptWork
  | .crypt => Env.runCryptWorkers
  | .sendOne => Env.runOneSendWorker
  | .clearOne => Env.runOneClearWorker
  | .sendAll => Env.runSendWorkers
  | .afterXmit => Env.afterXmit
  | .timerWorker timer => Env.timerWorker timer

  | .timers jHi => Env.runTimers jHi
  | .placeholder jHi => Env.runTimersPlaceholder jHi
  | .idle => Env.idleTimers
  | .advance ticks => Env.advance ticks
  | .afterAdvance => Env.afterAdvance

def observed : (call : EnvDeferredCall) → AuditM call.Result
  | .drained what queues => auditFocus (requireDrainedPrefix what queues)
  | .idleDevice => auditFocus requireIdleDevicePrefix
  | .noCrypt => liftPrefix Env.requireNoCryptWork
  | .crypt => runCryptWorkersAudit
  | .sendOne => runOneSendWorkerAudit
  | .clearOne => runOneClearWorkerAudit
  | .sendAll => runSendWorkersAudit
  | .afterXmit => afterXmitAudit
  | .timerWorker timer => liftPrefix (Env.timerWorker timer)

  | .timers jHi => runTimersAudit jHi
  | .placeholder jHi => runTimersPlaceholderAudit jHi
  | .idle => idleTimersAudit
  | .advance ticks => advanceAudit ticks
  | .afterAdvance => afterAdvanceAudit

theorem erases (call : EnvDeferredCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | drained what queues => exact auditFocus_erases (requireDrainedPrefix_erases what queues)
  | idleDevice => exact auditFocus_erases requireIdleDevicePrefix_erases
  | noCrypt => exact erasesPrefix_lift _
  | crypt => exact runCryptWorkersAudit_erases
  | sendOne => exact runOneSendWorkerAudit_erases
  | clearOne => exact runOneClearWorkerAudit_erases
  | sendAll => exact runSendWorkersAudit_erases
  | afterXmit => exact afterXmitAudit_erases
  | timerWorker timer => exact erasesPrefix_lift _

  | timers jHi => exact runTimersAudit_erases jHi
  | placeholder jHi => exact runTimersPlaceholderAudit_erases jHi
  | idle => exact idleTimersAudit_erases
  | advance ticks => exact advanceAudit_erases ticks
  | afterAdvance => exact afterAdvanceAudit_erases

theorem preserves (call : EnvDeferredCall) : PrefixPreserves AuditInv AuditSafe call.observed := by
  cases call with
  | drained what queues => exact auditFocus_preserves (requireDrainedPrefix_allocation what queues)
  | idleDevice => exact auditFocus_preserves requireIdleDevicePrefix_allocation
  | noCrypt => exact auditLift_store _ (requireNoCryptWork_sameKernel.of_factor (fun s : ProductStore43 => s.2.2.2) (fun w => wgStoreView w.wg) (fun _ => rfl))
  | crypt => exact runCryptWorkersAudit_preserves
  | sendOne => exact runOneSendWorkerAudit_preserves
  | clearOne => exact runOneClearWorkerAudit_preserves
  | sendAll => exact runSendWorkersAudit_preserves
  | afterXmit => exact afterXmitAudit_preserves
  | timerWorker timer => exact auditLift_store _ ((timerWorker_sameKernel timer).of_factor (fun s : ProductStore43 => s.2.2.2) (fun w => wgStoreView w.wg) (fun _ => rfl))

  | timers jHi => exact runTimersAudit_preserves jHi
  | placeholder jHi => exact runTimersPlaceholderAudit_preserves jHi
  | idle => exact idleTimersAudit_preserves
  | advance ticks => exact advanceAudit_preserves ticks
  | afterAdvance => exact afterAdvanceAudit_preserves

/-- Local allocation validity and empty history supply initial probe validity.
This does not supply the initialized outer Runner entry or its missing callers. -/
theorem from_allocation (call : EnvDeferredCall) (w : World) (hi : AllocationInv [] w.wg) :
    AuditSafe (runPrefix call.observed w []).2 ∧
    ∀ p ∈ probeEntries (runPrefix call.observed w []).2,
      AllocationInv p.history p.world.wg ∧
      (p.world.ambient.suspended.filterM Env.Activation.consistent).run p.world =
        (p.world.ambient.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
          (fun ys => (ys, p.world)) ∧
      ∀ a ∈ p.world.ambient.suspended, LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 := by
  have hs := (call.preserves w [] (audit_initial hi)).choose_spec.2.1
  exact ⟨hs, fun p hp => savedProbe_trials hs.2 hp⟩

end EnvDeferredCall
end Leanux.Proofs.WG.Lifetimes
