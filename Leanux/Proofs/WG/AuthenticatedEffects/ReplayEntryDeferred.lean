import Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntryActors
import Leanux.Proofs.WG.TransmitSecurity.NonceDeferredFrames

/-! Native deferred work and both timer modes carry each actual replay check
through scheduling, clears, delivery and stopped continuations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Keypairs TransmitSecurity.Driver Keypairs.WGFrames
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false

theorem wg_read : ProductSafe (liftPrefix getWG) :=
  product_storeLift _ (fun initial => productGetWG_spec (· = initial))

theorem wg_bookkeeping (f : WGWorld → WGWorld) (same : ∀ w, wgStoreView (f w) = wgStoreView w) :
    ProductSafe (liftPrefix (modifyWG f)) :=
  product_storeLift _ (fun initial => productModifyWG_spec (· = initial) f same)

theorem env_read : ProductSafe (liftPrefix getEnv) := by
  apply product_storeLift
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x v run
  cases run
  rfl

theorem deliver : ProductSafe hooks.deliver := product_same _ EnvFrames.deliverSent_sameSnapshot

macro "replay_deferred_native" : tactic => `(tactic| first
  | (replay_product_native getWG; exact wg_read)
  | (replay_product_native getEnv; exact env_read)
  | (replay_product_native modifyWG; apply wg_bookkeeping; intro w; rfl)
  | (replay_product_native liftWG
     apply product_wg
     first
     | (ordinary_head delTimer; exact SameView.ordinary (delTimer_sameSnapshot _ _))
     | (repeat' first | observer_ordinary_leaf | ordinary_strict_step))
  | (replay_product_native Env.runOneClearWorker; exact product_native _ EnvFrames.runOneClearWorker_ordinary)
  | (replay_product_native Env.requireDrained; exact product_storeLift _ (TransmitSecurity.Nonce.Frames.drained _ _))
  | (replay_product_native Env.requireNoCryptWork; exact product_same _ EnvFrames.requireNoCryptWork_sameSnapshot)
  | (replay_product_native Env.peekNextSite; exact product_same _ EnvFrames.peekNextSite_sameSnapshot)
  | (replay_product_native Env.timerWorker; exact product_same _ (EnvFrames.timerWorker_sameSnapshot _))
  | (replay_product_native Env.requireStepComplete; exact product_storeLift _ (TransmitSecurity.Nonce.Frames.step_complete _))
  | (replay_product_native Env.requireNothingDue; exact product_storeLift _ (TransmitSecurity.Nonce.Frames.nothing_due _))
  | (replay_product_native throw; exact product_throw _)
  | (first | replay_product_native getAmbient | replay_product_native modifyAmbient
           | replay_product_native recordBudget | replay_product_native peekUnit
           | replay_product_native peekSiteU64 | replay_product_native hiddenJiffies
           | replay_product_native invariant | replay_product_native unsupported
           | replay_product_native budgetExhausted
     exact product_ambient _))

macro "replay_deferred_step" : tactic => `(tactic| first
  | (replay_entry_head clearWorkerObserved
     rw [clearWorker_lift hooks rfl]
     exact product_native _ EnvFrames.runOneClearWorker_ordinary)
  | solve | replay_deferred_native
  | replay_entry_product_step)

theorem crypt : ProductSafe (cryptObserved hooks) :=
  product_bind (schedule none) (fun _ => deliver)

theorem send_workers : ProductSafe (sendWorkersObserved hooks) := by
  unfold sendWorkersObserved
  repeat' first
    | (replay_entry_head Hooks.deliver; exact deliver)
    | (replay_entry_head sendWorkerObserved; exact send_worker)
    | (replay_entry_head scheduleObserved; exact schedule _)
    | replay_deferred_step

theorem after_xmit : ProductSafe (afterXmitObserved hooks) := by
  unfold afterXmitObserved
  repeat' first
    | (replay_entry_head Hooks.deliver; exact deliver)
    | (replay_entry_head cryptObserved; exact crypt)
    | (replay_entry_head sendWorkersObserved; exact send_workers)
    | replay_deferred_step

theorem timer_section (worker : Worker) (body : PrefixM Event Unit)
    (safe : ProductSafe body) : ProductSafe (timerSectionObserved worker body) := by
  unfold timerSectionObserved
  dsimp only
  split
  · exact product_bind (product_ambient _) (fun _ => product_bind (product_ambient _) (fun _ =>
      runWorkerPrefix_preserves (fun _ _ hi => hi.2) product_store worker safe))
  · exact product_bind (product_ambient _) (fun _ =>
      runWorkerPrefix_preserves (fun _ _ hi => hi.2) product_store worker safe)

theorem timers (j : UInt64) : ProductSafe (timersObserved hooks j) := by
  unfold timersObserved
  repeat' first
    | (replay_entry_head Hooks.deliver; exact deliver)
    | (replay_entry_head sendWorkerObserved; exact send_worker)
    | (replay_entry_head Hooks.timerSelected; exact product_pure _)
    | (replay_entry_head Hooks.timerFinished; exact product_pure _)
    | (replay_entry_head cryptObserved; exact crypt)
    | (replay_entry_head timerSectionObserved; apply timer_section; exact product_state (timer _ _))
    | replay_deferred_step

theorem placeholder_timers (j : UInt64) : ProductSafe (placeholderTimersObserved hooks j) := by
  unfold placeholderTimersObserved
  repeat' first
    | (replay_entry_head Hooks.deliver; exact deliver)
    | (replay_entry_head Hooks.timerSelected; exact product_pure _)
    | (replay_entry_head Hooks.timerFinished; exact product_pure _)
    | (replay_entry_head cryptObserved; exact crypt)
    | (replay_entry_head sendWorkersObserved; exact send_workers)
    | (replay_entry_head timerSectionObserved; apply timer_section; exact product_state (timer _ _))
    | replay_deferred_step

theorem idle_timers : ProductSafe (idleTimersObserved hooks) := by
  unfold idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (replay_entry_head Hooks.deliver; exact deliver)
    | (replay_entry_head timersObserved; exact timers _)
    | (replay_entry_head placeholderTimersObserved; exact placeholder_timers _)
    | replay_deferred_step

theorem after_advance : ProductSafe (afterAdvanceObserved hooks) := by
  unfold afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (replay_entry_head Hooks.deliver; exact deliver)
    | (replay_entry_head timersObserved; exact timers _)
    | (replay_entry_head placeholderTimersObserved; exact placeholder_timers _)
    | replay_deferred_step

end Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
