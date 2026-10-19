import Leanux.Proofs.WG.TransmitSecurity.DriverWorkersProjection

namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
variable {E F : Type} {ρ : E → Option F} {g : Hooks E} {a : Hooks F}
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem crypt_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (cryptObserved g) (cryptObserved a) := by
  unfold cryptObserved
  repeat' first
    | (maintenance_head Hooks.deliver; exact h.deliver)
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head scheduleObserved; exact schedule_projects h _)
    | driver_product_step ρ

theorem sendWorkers_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (sendWorkersObserved g) (sendWorkersObserved a) := by
  unfold sendWorkersObserved
  repeat' first
    | (maintenance_head Hooks.deliver; exact h.deliver)
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head scheduleObserved; exact schedule_projects h _)
    | driver_product_step ρ

theorem afterXmit_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (afterXmitObserved g) (afterXmitObserved a) := by
  unfold afterXmitObserved
  repeat' first
    | (maintenance_head Hooks.deliver; exact h.deliver)
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head cryptObserved; exact crypt_projects h)
    | (maintenance_head sendWorkersObserved; exact sendWorkers_projects h)
    | driver_product_step ρ

theorem timerSection_projects (ρ : E → Option F) (worker : Worker)
    (body : PrefixM E Unit) (body' : PrefixM F Unit) (hb : ProjectsPrefix ρ id body body') :
    ProjectsPrefix ρ id (timerSectionObserved worker body) (timerSectionObserved worker body') := by
  unfold timerSectionObserved runWorkerPrefix
  repeat' first
    | (maintenance_head Hooks.deliver; exact h.deliver)
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | exact hb
    | driver_product_step ρ

theorem timers_projects (h : HooksProjects ρ g a) (j : UInt64) :
    ProjectsPrefix ρ id (timersObserved g j) (timersObserved a j) := by
  obtain ⟨scopeMap, enter, leave⟩ := h.timer
  unfold timersObserved
  repeat' first
    | (maintenance_head Hooks.deliver; exact h.deliver)
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head cryptObserved; exact crypt_projects h)
    | (maintenance_head timerSectionObserved
       apply timerSection_projects ρ
       exact (timer_projects h _ _).liftWGObserver ρ id)
    | (apply projectsPrefix_bind ρ scopeMap id (enter _ _ _ _ _); intro token)
    | (maintenance_head Hooks.timerFinished; exact leave _)
    | driver_product_step ρ

theorem placeholder_projects (h : HooksProjects ρ g a) (j : UInt64) :
    ProjectsPrefix ρ id (placeholderTimersObserved g j) (placeholderTimersObserved a j) := by
  obtain ⟨scopeMap, enter, leave⟩ := h.timer
  unfold placeholderTimersObserved
  repeat' first
    | (maintenance_head Hooks.deliver; exact h.deliver)
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head cryptObserved; exact crypt_projects h)
    | (maintenance_head sendWorkersObserved; exact sendWorkers_projects h)
    | (maintenance_head timerSectionObserved
       apply timerSection_projects ρ
       exact (timer_projects h _ _).liftWGObserver ρ id)
    | (apply projectsPrefix_bind ρ scopeMap id (enter _ _ _ _ _); intro token)
    | (maintenance_head Hooks.timerFinished; exact leave _)
    | driver_product_step ρ

theorem idleTimers_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (idleTimersObserved g) (idleTimersObserved a) := by
  unfold idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (maintenance_head Hooks.deliver; exact h.deliver)
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head timersObserved; exact timers_projects h _)
    | (maintenance_head placeholderTimersObserved; exact placeholder_projects h _)
    | driver_product_step ρ

theorem afterAdvance_projects (h : HooksProjects ρ g a) :
    ProjectsPrefix ρ id (afterAdvanceObserved g) (afterAdvanceObserved a) := by
  unfold afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (maintenance_head Hooks.deliver; exact h.deliver)
    | (maintenance_head Hooks.prepare; exact h.prepare)
    | (maintenance_head sendWorkerObserved; exact sendWorker_projects h)
    | (maintenance_head timersObserved; exact timers_projects h _)
    | (maintenance_head placeholderTimersObserved; exact placeholder_projects h _)
    | driver_product_step ρ

end Leanux.Proofs.WG.TransmitSecurity.Driver
