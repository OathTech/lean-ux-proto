import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierDeferredFrames

/-! The actual deferred and timer loops carry RX certificates through selected
callbacks, clear work, copied scheduler trials and every retained Stop prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues TransmitSecurity.Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option pp.structureInstances false
variable {E : Type} {extra : List E → Prop}
  {origin : E → Option TransportDriver.OriginEvent} {replay : E → Option TransportDriver.Replay}
  {hooks : Hooks E}

structure DeferredSafe (extra : List E → Prop) (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (hooks : Hooks E) : Prop extends
    WorkerSafe extra origin replay hooks, StagingSafe extra origin replay hooks where
  sendWorker : ProductSafe extra origin replay (sendWorkerObserved hooks)
  flushedSend : ∀ pid, StateSafe extra origin replay (hooks.flushedSend pid)
  selected : ∀ d j pid t we, ProductSafe extra origin replay (hooks.timerSelected d j pid t we)
  finished : ∀ token, ProductSafe extra origin replay (hooks.timerFinished token)

macro "transport_deferred_native" : tactic => `(tactic| first
  | (transport_product_native getWG; exact wg_read)
  | (transport_product_native getEnv; exact env_read)
  | (transport_product_native modifyWG; apply wg_bookkeeping; intro w; rfl)
  | (transport_product_native liftWG; apply product_wg; first
      | (snapshot_head delTimer; exact delTimer_rx _ _)
      | solve | transport_native_rx)
  | (transport_product_native Env.runOneClearWorker; exact clearOne)
  | (transport_product_native Env.requireDrained; exact product_storeLift _ (TransmitSecurity.Nonce.Frames.drained _ _))
  | (transport_product_native Env.requireNoCryptWork; exact product_storeLift _ requireNoCryptWork_sameKernel)
  | (transport_product_native Env.deliverSent; exact product_storeLift _ deliverSent_sameKernel)
  | (transport_product_native Env.peekNextSite; exact product_storeLift _ peekNextSite_sameKernel)
  | (transport_product_native Env.timerWorker; exact product_storeLift _ (timerWorker_sameKernel _))
  | (transport_product_native Env.requireStepComplete; exact product_storeLift _ (TransmitSecurity.Nonce.Frames.step_complete _))
  | (transport_product_native Env.requireNothingDue; exact product_storeLift _ (TransmitSecurity.Nonce.Frames.nothing_due _))
  | (transport_product_native throw; exact product_throw _)
  | (first | transport_product_native getAmbient | transport_product_native modifyAmbient
           | transport_product_native recordBudget | transport_product_native peekUnit
           | transport_product_native peekSiteU64 | transport_product_native hiddenJiffies
           | transport_product_native invariant | transport_product_native unsupported
           | transport_product_native budgetExhausted
     exact product_ambient _))

macro "transport_deferred_step" : tactic => `(tactic| first
  | solve | transport_deferred_native
  | (transport_carrier_head ForIn.forIn; first | apply product_range | apply product_forIn)
  | transport_carrier_product_step)

theorem crypt (h : DeferredSafe extra origin replay hooks) :
    ProductSafe extra origin replay (cryptObserved hooks) :=
  product_bind (schedule h.toWorkerSafe none) (fun _ => product_storeLift _ deliverSent_sameKernel)

theorem sendWorkers (h : DeferredSafe extra origin replay hooks) :
    ProductSafe extra origin replay (sendWorkersObserved hooks) := by
  unfold sendWorkersObserved
  repeat' first
    | (transport_carrier_head sendWorkerObserved; exact h.sendWorker)
    | (transport_carrier_head scheduleObserved; exact schedule h.toWorkerSafe _)
    | transport_deferred_step

theorem afterXmit (h : DeferredSafe extra origin replay hooks) :
    ProductSafe extra origin replay (afterXmitObserved hooks) := by
  unfold afterXmitObserved
  repeat' first
    | (transport_carrier_head cryptObserved; exact crypt h)
    | (transport_carrier_head sendWorkersObserved; exact sendWorkers h)
    | transport_deferred_step

theorem timerSection (worker : Worker) (body : PrefixM E Unit)
    (safe : ProductSafe extra origin replay body) :
    ProductSafe extra origin replay (timerSectionObserved worker body) := by
  unfold timerSectionObserved
  dsimp only
  split
  · exact product_bind (product_ambient _) (fun _ => product_bind (product_ambient _) (fun _ =>
      runWorkerPrefix_preserves (fun _ _ hi => hi.2) product_store worker safe))
  · exact product_bind (product_ambient _) (fun _ =>
      runWorkerPrefix_preserves (fun _ _ hi => hi.2) product_store worker safe)

theorem timers (h : DeferredSafe extra origin replay hooks) (j : UInt64) :
    ProductSafe extra origin replay (timersObserved hooks j) := by
  unfold timersObserved
  repeat' first
    | (transport_carrier_head sendWorkerObserved; exact h.sendWorker)
    | (transport_carrier_head Hooks.timerSelected; exact h.selected _ _ _ _ _)
    | (transport_carrier_head Hooks.timerFinished; exact h.finished _)
    | (transport_carrier_head cryptObserved; exact crypt h)
    | (transport_carrier_head timerSectionObserved
       apply timerSection
       exact product_state (timer h.toStagingSafe _ _))
    | transport_deferred_step

theorem placeholderTimers (h : DeferredSafe extra origin replay hooks) (j : UInt64) :
    ProductSafe extra origin replay (placeholderTimersObserved hooks j) := by
  unfold placeholderTimersObserved
  repeat' first
    | (transport_carrier_head Hooks.timerSelected; exact h.selected _ _ _ _ _)
    | (transport_carrier_head Hooks.timerFinished; exact h.finished _)
    | (transport_carrier_head cryptObserved; exact crypt h)
    | (transport_carrier_head sendWorkersObserved; exact sendWorkers h)
    | (transport_carrier_head timerSectionObserved
       apply timerSection
       exact product_state (timer h.toStagingSafe _ _))
    | transport_deferred_step

theorem idleTimers (h : DeferredSafe extra origin replay hooks) :
    ProductSafe extra origin replay (idleTimersObserved hooks) := by
  unfold idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (transport_carrier_head timersObserved; exact timers h _)
    | (transport_carrier_head placeholderTimersObserved; exact placeholderTimers h _)
    | transport_deferred_step

theorem afterAdvance (h : DeferredSafe extra origin replay hooks) :
    ProductSafe extra origin replay (afterAdvanceObserved hooks) := by
  unfold afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (transport_carrier_head timersObserved; exact timers h _)
    | (transport_carrier_head placeholderTimersObserved; exact placeholderTimers h _)
    | transport_deferred_step

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
