import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixScheduler
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDeferredFrames
import Leanux.Proofs.WG.AuthenticatedEffects.DeliveryPreservation
import Leanux.Proofs.WG.TransmitSecurity.NonceDeferredFrames

/-! Deferred bookkeeping retains all certified journal positions. Timer
selection and delivery markers append quiet events; timer callbacks still
need their own prefix contracts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

theorem range {β : Type} (r : Std.Legacy.Range) (initial : β) (body : Nat → β → PrefixM Event (ForInStep β))
    (checked : ∀ value acc, Checked (body value acc)) : Checked (forIn r initial body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact list _ initial body checked

theorem wg_read : Checked (liftPrefix getWG) :=
  product_store _ (fun initial => productGetWG_spec (· = initial))

theorem wg_bookkeeping (f : WGWorld → WGWorld) (same : ∀ w, wgStoreView (f w) = wgStoreView w) :
    Checked (liftPrefix (modifyWG f)) :=
  product_store _ (fun initial => productModifyWG_spec (· = initial) f same)

theorem env_read : Checked (liftPrefix getEnv) := by
  apply product_store
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w value v run
  cases run
  rfl

theorem enter (cause : Cause) : Checked (CausalScope.enterPrefix Event.scope cause) := by
  intro w h before
  exact bind_checked (emit (.scope (.entered ⟨h.length,cause⟩)) rfl (fun _ => rfl))
    (fun _ => pure_checked h.length) w h before

theorem timer_selected (d : Device) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) :
    Checked (hooks.timerSelected d bound pid timer entry) := by
  intro w h before
  exact bind_checked (emit (.old (.timerSelected ⟨d,bound,pid,timer,entry,w⟩)) rfl (fun _ => rfl))
    (fun _ => enter (.timer bound pid timer entry)) w h before

theorem timer_finished (token : Nat) : Checked (hooks.timerFinished token) := emit _ rfl (fun _ => rfl)

theorem delivery : Checked hooks.deliver := by
  unfold Driver.Hooks.deliver CausalJournal.hooks DeliverySource.observed
  exact bind_checked wg_read (fun w => bind_checked (emit (.delivery w.sent) rfl (fun _ => rfl))
    (fun _ => product_store _ deliverSent_sameKernel))

theorem delete_timer (pid : PeerId) (timer : PeerTimer) :
    StateChecked (liftWGPrefix (delTimer pid timer)) :=
  StateEnsures.quiet (CompleteProduct.delete_timer pid timer) (fun _ _ _=>rfl)

macro "prefix_deferred_native" : tactic => `(tactic| first
  | (prefix_product_native getWG; exact wg_read)
  | (prefix_product_native getEnv; exact env_read)
  | (prefix_product_native modifyWG; apply wg_bookkeeping; intro w; rfl)
  | (prefix_product_wg delTimer; exact wg _ (delete_timer _ _))
  | (prefix_product_native Env.requireDrained; exact product_store _ (TransmitSecurity.Nonce.Frames.drained _ _))
  | (prefix_product_native Env.requireNoCryptWork; exact product_store _ requireNoCryptWork_sameKernel)
  | (prefix_product_head Driver.Hooks.deliver; exact delivery)
  | (prefix_product_native Env.deliverSent; exact product_store _ deliverSent_sameKernel)
  | (prefix_product_native Env.peekNextSite; exact product_store _ peekNextSite_sameKernel)
  | (prefix_product_native Env.timerWorker; exact product_store _ (timerWorker_sameKernel _))
  | (prefix_product_native Env.requireStepComplete; exact product_store _ (TransmitSecurity.Nonce.Frames.step_complete _))
  | (prefix_product_native Env.requireNothingDue; exact product_store _ (TransmitSecurity.Nonce.Frames.nothing_due _))
  | (first | prefix_product_native recordBudget | prefix_product_native peekUnit
           | prefix_product_native peekSiteU64 | prefix_product_native hiddenJiffies
           | prefix_product_native unsupported | prefix_product_native budgetExhausted
     exact ambient _)
  | prefix_scheduler_native)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
