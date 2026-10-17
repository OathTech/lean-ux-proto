import Leanux.Proofs.WG.Keypairs.Evolution.Scheduler
import Leanux.Proofs.Logged.Operations
import Leanux.Proofs.WG.Keypairs.Frames.Env

/-! Evolution through receive-capable environment operations. These contracts
cover all successful original observer runs, including placeholder branches. -/
namespace Leanux.Proofs.WG.Keypairs.OperationObservers
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged
open Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.Observers
open Leanux.Proofs.WG.Keypairs.SchedulerObservers
open Std.Do Leanux.Proofs.Framing
open WGFrames WGTransitions WGMore EnvFrames

set_option maxHeartbeats 400000
set_option pp.structureInstances false


private theorem requireStepComplete_ordinary (b : UInt64) :
    ProductOrdinaryAction (Env.requireStepComplete b) := by
  apply SameView.ordinary
  intro initial
  change Preserves (fun w : World => snapshot w.wg = initial) (Env.requireStepComplete b)
  have dev := (sameView_liftWG (fun w => snapshot w.wg) snapshot getDev
    getDev_sameSnapshot (fun _ _ _ h => h)).wp (fun value => value = initial)
  unfold Env.requireStepComplete
  apply preserves_bind dev
  intro d
  cases TimerWheel.anotherAtStep d b with
  | none => exact preserves_pure _
  | some due =>
    rcases due with ⟨pid, t⟩
    exact hoare_throw _

private theorem requireNothingDue_ordinary (b : UInt64) :
    ProductOrdinaryAction (Env.requireNothingDue b) := by
  apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run _ _ _).mpr
  intro w x w' hr
  have read (s : World) : (getWG : Leanux.M WGWorld).run s = .ok (s.wg, s) := rfl
  unfold Env.requireNothingDue at hr
  simp only [StateT.run_bind, read, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
  cases hd : w.wg.dev with
  | none =>
    simp only [hd, StateT.run_pure] at hr
    cases hr
    exact .refl _
  | some d =>
    simp only [hd] at hr
    cases hn : TimerWheel.nextDue d b with
    | none =>
      simp only [hn, StateT.run_pure] at hr
      cases hr
      exact .refl _
    | some due =>
      rcases due with ⟨pid, t, we⟩
      simp only [hn, StateT.run_bind] at hr
      cases hw : (Env.timerWorker t).run w with
      | error e =>
        rw [hw] at hr
        cases hr
      | ok out =>
        rcases out with ⟨worker, w1⟩
        simp only [hw, Leanux.Proofs.WG.CounterWindow.except_ok_bind, read] at hr
        cases hs : (Env.sectionAppearsLater worker
          (((w1.wg.timerUnits.find? fun e => e.2.1 == pid && e.2.2 == t).map (·.1)).getD 0)).run w1 with
        | error e =>
          rw [hs] at hr
          cases hr
        | ok out =>
          rcases out with ⟨later, w2⟩
          simp only [hs, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
          cases later <;> cases hr

private theorem operationRouting (a : Net.M α) :
    OrdinaryAction (MonadLift.monadLift a : WG.M α) := by
  apply SameView.ordinary
  intro initial
  exact hoare_liftRouting a (fun w => snapshot w = initial) (fun _ _ h => h)

macro "operation_leaf_step" : tactic => `(tactic|
  first
    | (evolves_head handshakeReceiveWorkerLogged;
        refine handshakeReceiveWorkerLogged_evolves _ ?_)
    | (evolves_head nestedReschedLogged; exact nestedReschedLogged_evolves _)
    | (evolves_head scheduleLogged; exact scheduleLogged_evolves _)
    | (evolves_head runCryptWorkersLogged; exact runCryptWorkersLogged_evolves)
    | (evolves_head napiSoftirqLogged; exact napiSoftirqLogged_evolves)
    | (evolves_head rxPollLogged; refine rxPollLogged_evolves _ _ _ ?_
       intro packets
       exact evolves_liftM (ordinary_forM packets Env.deliverInner deliverInner_ordinary))
    | (evolves_head Leanux.getRouting; unfold Leanux.getRouting)
    | (evolves_head Leanux.getWG; unfold Leanux.getWG)
    | (evolves_head Leanux.modifyWG; unfold Leanux.modifyWG)
    | (ordinary_head Leanux.getWG; unfold Leanux.getWG)
    | (ordinary_head Leanux.modifyWG; unfold Leanux.modifyWG)
    | (ordinary_head Env.requireStepComplete; exact requireStepComplete_ordinary _)
    | (ordinary_head Env.requireNothingDue; exact requireNothingDue_ordinary _)
    | (ordinary_head WG.requireNotPending; exact SameView.ordinary (requireNotPending_sameSnapshot _ _))
    | (ordinary_head Env.requireDrained; exact SameView.ordinary (requireDrained_sameSnapshot _ _))
    | (ordinary_head Env.requireNoCryptWork; exact SameView.ordinary requireNoCryptWork_sameSnapshot)
    | (ordinary_head Env.runOneSendWorker; exact SameView.ordinary runOneSendWorker_sameSnapshot)
    | (ordinary_head Env.peekNextSite; exact SameView.ordinary peekNextSite_sameSnapshot)
    | (ordinary_head Env.runOneClearWorker; exact runOneClearWorker_ordinary)
    | (ordinary_head Env.timerWorker; exact SameView.ordinary (timerWorker_sameSnapshot _))
    | (ordinary_head Env.runTimerSection; refine runTimerSection_ordinary _ _ ?_)
    | (ordinary_head WG.timerCallback; exact timerCallback_ordinary _ _)
    | (ordinary_head WG.delTimer; exact SameView.ordinary (delTimer_sameSnapshot _ _))
    | (ordinary_head Env.fixtureSend; exact SameView.ordinary fixtureSend_sameSnapshot)
    | (ordinary_head Env.senderSource; exact SameView.ordinary (senderSource_sameSnapshot _ _ _ _))
    | (ordinary_head WG.wgReceive; exact wgReceive_ordinary _ _)
    | (ordinary_head MonadLift.monadLift; exact operationRouting _)
    | (ordinary_head liftM; exact operationRouting _)
    | scheduler_worker_step
    | env_product_step)

macro "operation_structure_step" : tactic => `(tactic|
  first
    | intro_forall
    | evolves_join_let
    | evolves_join_use
    | (evolves_head Bind.bind; refine evolves_bind ?_ ?_)
    | (evolves_head Pure.pure; exact evolves_pure _)
    | (evolves_head MonadExceptOf.throw; exact evolves_throw _)
    | (evolves_head ite; refine evolves_ite _ ?_ ?_)
    | (evolves_head Functor.discard; refine evolves_discard ?_)
    | (evolves_head Functor.map; refine evolves_map _ ?_)
    | (evolves_head ForIn.forIn; with_reducible refine evolves_range _ _ _ ?_)
    | (evolves_head ForIn.forIn; with_reducible refine evolves_forIn _ _ _ ?_)
    | evolves_head_reduce
    | evolves_head_match)

theorem runSendWorkersLogged_evolves  : Evolves (runSendWorkersLogged) := by
  unfold runSendWorkersLogged
  repeat' first
    | operation_leaf_step

theorem afterXmitLogged_evolves  : Evolves (afterXmitLogged) := by
  unfold afterXmitLogged
  repeat' first
    | (evolves_head runSendWorkersLogged; exact runSendWorkersLogged_evolves)
    | operation_leaf_step

theorem runTimersLogged_evolves (jHi : UInt64) : Evolves (runTimersLogged jHi) := by
  unfold runTimersLogged
  repeat' first | operation_structure_step | operation_leaf_step
  all_goals exact evolves_throw _


theorem runTimersPlaceholderLogged_evolves (jHi : UInt64) : Evolves (runTimersPlaceholderLogged jHi) := by
  unfold runTimersPlaceholderLogged
  repeat' first
    | (evolves_head runSendWorkersLogged; exact runSendWorkersLogged_evolves)
    | (evolves_head afterXmitLogged; exact afterXmitLogged_evolves)
    | (evolves_head runTimersLogged; exact runTimersLogged_evolves _)
    | operation_leaf_step

theorem idleTimersLogged_evolves  : Evolves (idleTimersLogged) := by
  unfold idleTimersLogged
  repeat' first
    | (evolves_head runSendWorkersLogged; exact runSendWorkersLogged_evolves)
    | (evolves_head afterXmitLogged; exact afterXmitLogged_evolves)
    | (evolves_head runTimersLogged; exact runTimersLogged_evolves _)
    | (evolves_head runTimersPlaceholderLogged; exact runTimersPlaceholderLogged_evolves _)
    | operation_leaf_step
  all_goals exact evolves_throw _

theorem afterAdvanceLogged_evolves  : Evolves (afterAdvanceLogged) := by
  unfold afterAdvanceLogged
  repeat' first
    | (evolves_head runSendWorkersLogged; exact runSendWorkersLogged_evolves)
    | (evolves_head afterXmitLogged; exact afterXmitLogged_evolves)
    | (evolves_head runTimersLogged; exact runTimersLogged_evolves _)
    | (evolves_head runTimersPlaceholderLogged; exact runTimersPlaceholderLogged_evolves _)
    | (evolves_head idleTimersLogged; exact idleTimersLogged_evolves)
    | operation_leaf_step
  all_goals exact evolves_throw _

theorem observeLogged_evolves  : Evolves (observeLogged) := by
  unfold observeLogged
  repeat' first
    | (evolves_head runSendWorkersLogged; exact runSendWorkersLogged_evolves)
    | (evolves_head afterXmitLogged; exact afterXmitLogged_evolves)
    | (evolves_head runTimersLogged; exact runTimersLogged_evolves _)
    | (evolves_head runTimersPlaceholderLogged; exact runTimersPlaceholderLogged_evolves _)
    | (evolves_head idleTimersLogged; exact idleTimersLogged_evolves)
    | (evolves_head afterAdvanceLogged; exact afterAdvanceLogged_evolves)
    | operation_leaf_step

macro "operation_step" : tactic => `(tactic|
  first
    | (evolves_head runSendWorkersLogged; exact runSendWorkersLogged_evolves)
    | (evolves_head afterXmitLogged; exact afterXmitLogged_evolves)
    | (evolves_head runTimersLogged; exact runTimersLogged_evolves _)
    | (evolves_head runTimersPlaceholderLogged; exact runTimersPlaceholderLogged_evolves _)
    | (evolves_head idleTimersLogged; exact idleTimersLogged_evolves)
    | (evolves_head afterAdvanceLogged; exact afterAdvanceLogged_evolves)
    | (evolves_head observeLogged; exact observeLogged_evolves)
    | operation_leaf_step)

theorem injectLogged_evolves (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    Evolves (injectLogged family port msg tos ll dest) := by
  unfold injectLogged
  repeat' first | operation_structure_step | operation_step


theorem pollScheduledInlineLogged_evolves : Evolves pollScheduledInlineLogged := by
  unfold pollScheduledInlineLogged
  repeat' operation_step

theorem afterBatchLogged_evolves : Evolves afterBatchLogged := by
  unfold afterBatchLogged
  repeat' operation_step

theorem floodLogged_evolves (count port family : Nat) (messages : List (List UInt8)) :
    Evolves (floodLogged count port family messages) := by
  unfold floodLogged
  repeat' first
    | (evolves_head afterBatchLogged; exact afterBatchLogged_evolves)
    | (evolves_head pollScheduledInlineLogged; exact pollScheduledInlineLogged_evolves)
    | operation_step

end Leanux.Proofs.WG.Keypairs.OperationObservers
