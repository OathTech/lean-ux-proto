import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionCarrier

/-! Real deferred send and timer dispatch carry live origins and certify each
selection at its guarded source position, including prefixes before Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections.Carrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing TransmitSecurity Queues Lifetimes
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

macro "selection_deferred_step" : tactic => `(tactic| first
  | (selection_carrier_head liftPrefix; apply product_native; solve | causal_delayed_deferred_native)
  | (selection_carrier_head Driver.sendWorkerObserved; exact Selections.send_worker)
  | (selection_carrier_head Driver.scheduleObserved; exact schedule _)
  | selection_carrier_step)

theorem crypt : ProductSafe (Driver.cryptObserved hooks) :=
  product_bind (schedule none) (fun _ => product_native _
    (Delayed.product_store_lift _ deliverSent_sameKernel))

theorem sendWorkers : ProductSafe (Driver.sendWorkersObserved hooks) := by
  unfold Driver.sendWorkersObserved
  repeat' selection_deferred_step

theorem afterXmit : ProductSafe (Driver.afterXmitObserved hooks) := by
  unfold Driver.afterXmitObserved
  repeat' first
    | (selection_carrier_head Driver.cryptObserved; exact crypt)
    | (selection_carrier_head Driver.sendWorkersObserved; exact sendWorkers)
    | selection_deferred_step

theorem timerSection (worker : Worker) (body : PrefixM Event Unit) (safe : ProductSafe body) :
    ProductSafe (Driver.timerSectionObserved worker body) := by
  unfold Driver.timerSectionObserved
  dsimp only
  split
  · exact product_bind (product_native _ (Delayed.product_ambient _)) (fun _ =>
      product_bind (product_native _ (Delayed.product_ambient _)) (fun _ =>
        runWorkerPrefix_preserves (fun _ _ hi => hi.2) product_store worker safe))
  · exact product_bind (product_native _ (Delayed.product_ambient _)) (fun _ =>
      runWorkerPrefix_preserves (fun _ _ hi => hi.2) product_store worker safe)

abbrev AfterDevice (d : Device) (body : PrefixM Event α) :=
  PrefixEnsures (fun h w => Inv h w.wg ∧ w.wg.dev = some d) Safe body
    (fun _ h w => Inv h w.wg)

theorem after_device (d : Device) (body : PrefixM Event α) (safe : ProductSafe body) : AfterDevice d body :=
  PrefixEnsures.consequence (Q := fun _ h (w : World) => Inv h w.wg) safe (fun _ _ hi => hi.1) (fun _ _ _ hi => hi)

theorem getDev_bind (tail : Device → PrefixM Event α) (safe : ∀ d, AfterDevice d (tail d)) :
    ProductSafe (liftPrefix (liftWG getDev) >>= tail) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.bind (Q := fun d h w => Inv h w.wg ∧ w.wg.dev = some d)
  · have native : StatePrefixEnsures (fun h w _ => Inv h w) Safe (liftWGPrefix getDev)
        (fun d h w _ => Inv h w ∧ w.dev = some d) := by
      apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.2)
      intro h w a d v b hi run
      obtain ⟨rfl,rfl,device⟩ := RxCredits.DecryptCarrier.getDev_current a b run
      exact ⟨hi,device⟩
    simpa only [liftWGObserver_lift] using native.liftWGObserver
  · exact safe

theorem selected_bind (d : Device) (bound : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry)
    (due : TimerWheel.nextDue d bound = some (pid,timer,entry))
    (tail : Nat → PrefixM Event α) (safe : ∀ token, ProductSafe (tail token)) :
    AfterDevice d (hooks.timerSelected d bound pid timer entry >>= tail) :=
  PrefixEnsures.bind ((Selections.timer_selected d bound pid timer entry).consequence
    (fun _ _ hi => ⟨hi.1,hi.2,due⟩) (fun _ _ _ hi => hi)) safe

open Lean Meta Elab Tactic in
elab "selection_read_bind" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductSafe do throwError "not a product contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let first := action.getAppArgs[action.getAppArgs.size - 2]!
  unless first.isAppOf ``liftPrefix do throwError "not a native lift"
  let native := first.getAppArgs.back!
  unless native.isAppOf ``liftWG && native.getAppArgs.back!.isAppOf ``getDev do
    throwError "not the saved-device getter"
  evalTactic (← `(tactic| apply getDev_bind))

open Lean Meta Elab Tactic in
elab "selection_forget_device" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``AfterDevice do throwError "not a saved-device continuation"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  if action.isAppOf ``Bind.bind then
    let first := action.getAppArgs[action.getAppArgs.size - 2]!
    if first.isAppOf ``Driver.Hooks.timerSelected then throwError "selection still needs its saved device"
  else unless action.isAppOf ``Pure.pure || action.isAppOf ``ForIn.forIn do
    throwError "split the saved-device choice first"
  evalTactic (← `(tactic| apply after_device))

macro "selection_timer_step" : tactic => `(tactic| first
  | (selection_carrier_head Driver.cryptObserved; exact crypt)
  | (selection_carrier_head Driver.sendWorkersObserved; exact sendWorkers)
  | (selection_carrier_head Driver.Hooks.timerFinished; exact Selections.timer_finished _)
  | (selection_carrier_head Driver.timerSectionObserved; apply timerSection; exact product_state (timer_callback _ _))
  | selection_deferred_step)

theorem placeholderTimers (bound : UInt64) : ProductSafe (Driver.placeholderTimersObserved hooks bound) := by
  unfold Driver.placeholderTimersObserved
  repeat' first
    | selection_read_bind
    | (apply selected_bind; assumption)
    | selection_forget_device
    | selection_timer_step
    | maintenance_intro
    | (split; all_goals try simp_all only []; all_goals try subst_vars)

theorem timers (bound : UInt64) : ProductSafe (Driver.timersObserved hooks bound) := by
  unfold Driver.timersObserved
  repeat' first
    | selection_read_bind
    | (apply selected_bind; assumption)
    | selection_forget_device
    | selection_timer_step
    | maintenance_intro
    | (split; all_goals try simp_all only []; all_goals try subst_vars)

theorem idleTimers :
    ProductSafe (Driver.idleTimersObserved hooks) := by
  unfold Driver.idleTimersObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (selection_carrier_head Driver.timersObserved; exact timers _)
    | (selection_carrier_head Driver.placeholderTimersObserved; exact placeholderTimers _)
    | selection_deferred_step

theorem afterAdvance :
    ProductSafe (Driver.afterAdvanceObserved hooks) := by
  unfold Driver.afterAdvanceObserved
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (selection_carrier_head Driver.timersObserved; exact timers _)
    | (selection_carrier_head Driver.placeholderTimersObserved; exact placeholderTimers _)
    | selection_deferred_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections.Carrier
