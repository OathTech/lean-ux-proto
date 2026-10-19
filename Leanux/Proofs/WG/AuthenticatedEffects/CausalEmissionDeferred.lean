import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionDeferredBase

/-! Every actual deferred delivery retains its pre-clear occurrence
certificate, including a Stop inside delivery. Timer and work callbacks use
the same observed socket paths and paired live/history carrier. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries.Carrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity.Driver
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option pp.structureInstances false

macro "emission_deferred_step" : tactic => `(tactic| first
  | solve | emission_deferred_native
  | emission_carrier_product_step)

theorem crypt : ProductSafe (cryptObserved hooks) :=
  product_bind (schedule none) (fun _ => deliver)

theorem send_workers : ProductSafe (sendWorkersObserved hooks) := by
  unfold sendWorkersObserved
  repeat' first
    | (emission_carrier_head Hooks.deliver; exact deliver)
    | (emission_carrier_head sendWorkerObserved; exact send_worker)
    | (emission_carrier_head scheduleObserved; exact schedule _)
    | emission_deferred_step

theorem after_xmit : ProductSafe (afterXmitObserved hooks) := by
  unfold afterXmitObserved
  repeat' first
    | (emission_carrier_head Hooks.deliver; exact deliver)
    | (emission_carrier_head cryptObserved; exact crypt)
    | (emission_carrier_head sendWorkersObserved; exact send_workers)
    | emission_deferred_step

theorem timer_section (worker : Worker) (body : PrefixM Event Unit) (safe : ProductSafe body) :
    ProductSafe (timerSectionObserved worker body) := by
  unfold timerSectionObserved
  dsimp only
  split
  · exact product_bind (ambient _) (fun _ => product_bind (ambient _) (fun _ => run_worker worker body safe))
  · exact product_bind (ambient _) (fun _ => run_worker worker body safe)

theorem timers (j : UInt64) : ProductSafe (timersObserved hooks j) := by
  unfold timersObserved
  repeat' first
    | (emission_carrier_head Hooks.deliver; exact deliver)
    | (emission_carrier_head sendWorkerObserved; exact send_worker)
    | (emission_carrier_head Hooks.timerSelected; exact timer_selected _ _ _ _ _)
    | (emission_carrier_head Hooks.timerFinished; exact timer_finished _)
    | (emission_carrier_head cryptObserved; exact crypt)
    | (emission_carrier_head timerSectionObserved
       apply timer_section
       exact product_state (timer _ _))
    | emission_deferred_step

theorem placeholder_timers (j : UInt64) : ProductSafe (placeholderTimersObserved hooks j) := by
  unfold placeholderTimersObserved
  repeat' first
    | (emission_carrier_head Hooks.deliver; exact deliver)
    | (emission_carrier_head Hooks.timerSelected; exact timer_selected _ _ _ _ _)
    | (emission_carrier_head Hooks.timerFinished; exact timer_finished _)
    | (emission_carrier_head cryptObserved; exact crypt)
    | (emission_carrier_head sendWorkersObserved; exact send_workers)
    | (emission_carrier_head timerSectionObserved
       apply timer_section
       exact product_state (timer _ _))
    | emission_deferred_step

theorem idle_timers : ProductSafe (idleTimersObserved hooks) := by
  unfold idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (emission_carrier_head Hooks.deliver; exact deliver)
    | (emission_carrier_head timersObserved; exact timers _)
    | (emission_carrier_head placeholderTimersObserved; exact placeholder_timers _)
    | emission_deferred_step

theorem after_advance : ProductSafe (afterAdvanceObserved hooks) := by
  unfold afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (emission_carrier_head Hooks.deliver; exact deliver)
    | (emission_carrier_head timersObserved; exact timers _)
    | (emission_carrier_head placeholderTimersObserved; exact placeholder_timers _)
    | emission_deferred_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions.Deliveries.Carrier
