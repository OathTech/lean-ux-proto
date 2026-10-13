import Leanux.Proofs.WG.Keypairs.Evolution.Scheduler
import Leanux.Proofs.Logged.Operations
import Leanux.Proofs.WG.Keypairs.Frames.Env

/-! Evolution through receive-capable environment operations. These contracts
cover all successful original observer runs, including placeholder branches. -/
namespace Leanux.Proofs.WG.Keypairs.OperationObservers
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged
open Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.Observers
open Leanux.Proofs.WG.Keypairs.SchedulerObservers
open KernelFrames WGFrames WGTransitions WGMore EnvFrames

set_option maxHeartbeats 400000
set_option pp.structureInstances false

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
    | (ordinary_head Leanux.getK; exact getK_sameSnapshot.ordinary)
    | (ordinary_head WG.requireNotPending; exact (requireNotPending_sameSnapshot _ _).ordinary)
    | (ordinary_head Env.requireDrained; exact (requireDrained_sameSnapshot _ _).ordinary)
    | (ordinary_head Env.requireNoCryptWork; exact requireNoCryptWork_sameSnapshot.ordinary)
    | (ordinary_head Env.runOneSendWorker; exact runOneSendWorker_sameSnapshot.ordinary)
    | (ordinary_head Env.peekNextSite; exact peekNextSite_sameSnapshot.ordinary)
    | (ordinary_head Env.fireTimer; exact fireTimer_ordinary _ _)
    | (ordinary_head Env.runOneClearWorker; exact runOneClearWorker_ordinary)
    | (ordinary_head Env.timerWorker; exact (timerWorker_sameSnapshot _).ordinary)
    | (ordinary_head Env.runTimerSection; refine runTimerSection_ordinary _ _ ?_)
    | (ordinary_head WG.timerCallback; exact timerCallback_ordinary _ _)
    | (ordinary_head WG.delTimer; exact (delTimer_sameSnapshot _ _).ordinary)
    | (ordinary_head Env.fixtureSend; exact fixtureSend_sameSnapshot.ordinary)
    | (ordinary_head Env.senderSource; exact (senderSource_sameSnapshot _ _ _ _).ordinary)
    | (ordinary_head Leanux.discardFloodRecords; exact (discardFloodRecords_sameSnapshot _ _).ordinary)
    | (ordinary_head Leanux.floodTailEffect; exact (floodTailEffect_sameSnapshot _ _ _).ordinary)
    | (ordinary_head WG.wgReceive; exact wgReceive_ordinary _ _)
    | scheduler_worker_step)

theorem runSendWorkersLogged_evolves  : Evolves (runSendWorkersLogged) := by
  unfold runSendWorkersLogged
  repeat' first
    | operation_leaf_step

theorem afterXmitLogged_evolves  : Evolves (afterXmitLogged) := by
  unfold afterXmitLogged
  repeat' first
    | (evolves_head runSendWorkersLogged; exact runSendWorkersLogged_evolves)
    | operation_leaf_step

theorem runTimersLogged_evolves (jHi : Nat) : Evolves (runTimersLogged jHi) := by
  unfold runTimersLogged
  repeat' first
    | (evolves_head runSendWorkersLogged; exact runSendWorkersLogged_evolves)
    | (evolves_head afterXmitLogged; exact afterXmitLogged_evolves)
    | operation_leaf_step

theorem runTimersPlaceholderLogged_evolves (jHi : Nat) : Evolves (runTimersPlaceholderLogged jHi) := by
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

theorem afterAdvanceLogged_evolves  : Evolves (afterAdvanceLogged) := by
  unfold afterAdvanceLogged
  repeat' first
    | (evolves_head runSendWorkersLogged; exact runSendWorkersLogged_evolves)
    | (evolves_head afterXmitLogged; exact afterXmitLogged_evolves)
    | (evolves_head runTimersLogged; exact runTimersLogged_evolves _)
    | (evolves_head runTimersPlaceholderLogged; exact runTimersPlaceholderLogged_evolves _)
    | (evolves_head idleTimersLogged; exact idleTimersLogged_evolves)
    | operation_leaf_step

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
  repeat' operation_step

theorem floodLogged_evolves (count port : Nat) (messages : List (List UInt8)) :
    Evolves (floodLogged count port messages) := by
  unfold floodLogged
  repeat' operation_step
  all_goals exact evolves_throw _

theorem pollScheduledInlineLogged_evolves : Evolves pollScheduledInlineLogged := by
  unfold pollScheduledInlineLogged
  repeat' operation_step

end Leanux.Proofs.WG.Keypairs.OperationObservers
