import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryWorkers

namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
variable {E : Type} {Safe : List E → Prop} {g : Hooks E}
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem crypt_history (h : ActorHistorySafe Safe g) :
    ProductHistorySafe Safe (cryptObserved g) := by
  unfold cryptObserved
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head scheduleObserved; exact schedule_history h _)
    | driver_product_history_step

theorem sendWorkers_history (h : ActorHistorySafe Safe g) :
    ProductHistorySafe Safe (sendWorkersObserved g) := by
  unfold sendWorkersObserved
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head scheduleObserved; exact schedule_history h _)
    | driver_product_history_step

theorem afterXmit_history (h : ActorHistorySafe Safe g) :
    ProductHistorySafe Safe (afterXmitObserved g) := by
  unfold afterXmitObserved
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head cryptObserved; exact crypt_history h)
    | (driver_history_head sendWorkersObserved; exact sendWorkers_history h)
    | driver_product_history_step

theorem timerSection_history (worker : Worker)
    (body : PrefixM E Unit) (hb : ProductHistorySafe Safe body) :
    ProductHistorySafe Safe (timerSectionObserved worker body) := by
  unfold timerSectionObserved runWorkerPrefix
  repeat' first
    | exact hb
    | driver_product_history_step

theorem timers_history (h : ActorHistorySafe Safe g) (j : UInt64) :
    ProductHistorySafe Safe (timersObserved g j) := by
  unfold timersObserved
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head cryptObserved; exact crypt_history h)
    | (driver_history_head timerSectionObserved
       apply timerSection_history
       exact (timer_history h _ _).liftWGObserver)
    | (driver_history_head Hooks.timerSelected; exact h.timerSelected _ _ _ _ _)
    | driver_product_history_step

theorem placeholder_history (h : ActorHistorySafe Safe g) (j : UInt64) :
    ProductHistorySafe Safe (placeholderTimersObserved g j) := by
  unfold placeholderTimersObserved
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head cryptObserved; exact crypt_history h)
    | (driver_history_head sendWorkersObserved; exact sendWorkers_history h)
    | (driver_history_head timerSectionObserved
       apply timerSection_history
       exact (timer_history h _ _).liftWGObserver)
    | (driver_history_head Hooks.timerSelected; exact h.timerSelected _ _ _ _ _)
    | driver_product_history_step

theorem idleTimers_history (h : ActorHistorySafe Safe g) :
    ProductHistorySafe Safe (idleTimersObserved g) := by
  unfold idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head timersObserved; exact timers_history h _)
    | (driver_history_head placeholderTimersObserved; exact placeholder_history h _)
    | driver_product_history_step

theorem afterAdvance_history (h : ActorHistorySafe Safe g) :
    ProductHistorySafe Safe (afterAdvanceObserved g) := by
  unfold afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (driver_history_head Hooks.prepare; exact h.prepare)
    | (driver_history_head sendWorkerObserved; exact h.sendWorker)
    | (driver_history_head timersObserved; exact timers_history h _)
    | (driver_history_head placeholderTimersObserved; exact placeholder_history h _)
    | driver_product_history_step

end Leanux.Proofs.WG.TransmitSecurity.Driver
