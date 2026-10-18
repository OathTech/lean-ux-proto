import Leanux.Proofs.WG.Queues.RxCompletionCallers
import Leanux.Proofs.WG.Queues.RxSyscallsHistory

/-! Completion pairing through the existing environment and syscall observers.
Every exact flood producer, inline batch polls, recorded/placeholder timer suffixes and
normal negative syscall returns retain their concrete callback continuations. -/
namespace Leanux.Proofs.WG.Queues.RxCompletion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

/- Guard the actual observer before composing its unchanged product-history
contract. Shared continuations are checked once at their source binders. -/
open Lean Meta Elab Tactic in
elab "completion_env_match" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless target.isAppOf ``PrefixEnsures && args.size ≥ 2 do
    throwError "not a completion endpoint contract"
  let action := args[args.size-2]!.consumeMData
  let some _ ← matchMatcherApp? action | throwError "not an observer match"
  replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)

macro "completion_env_steps" : tactic => `(tactic| first
  | maintenance_intro
  | maintenance_reduce
  | maintenance_reduce_match
  | maintenance_join_let
  | maintenance_join_use
  | (audit_contract_head RxHistory.audit; exact audit_quiet _)
  | (audit_contract_head RxHistory.mixed; exact mixed_quiet _)
  | (audit_contract_head Origins.HistoryAdapters.prepare; exact prepare_quiet)
  | (audit_contract_head Origins.HistoryAdapters.receiveIteration; exact receiveIteration_quiet)
  | (audit_contract_head liftPrefix; exact lift_quiet _)
  | (audit_contract_head Pure.pure; exact PrefixPreserves.pure closed_safe _)
  | (audit_contract_head Bind.bind; apply PrefixEnsures.bind
      (Q := fun _ h (_ : World) => Closed historyEvent h))
  | (audit_contract_head ForIn.forIn; first
      | apply PrefixEnsures.rangeInvariant (State := World)
          (I := fun _ h _ => Closed historyEvent h) (hs := fun _ _ _ hi => hi.prefix)
      | apply PrefixEnsures.forInInvariant (State := World)
          (I := fun _ h _ => Closed historyEvent h) (hs := fun _ _ _ hi => hi.prefix))
  | ((first | audit_contract_head ite | audit_contract_head dite); split)
  | completion_env_match
  | contradiction)

theorem runWorker_preserves (worker : Worker) (body : RxHistory.Obs Unit)
    (hb : Preserves historyEvent body) : Preserves historyEvent (runWorkerPrefix worker body) :=
  runWorkerPrefix_preserves closed_safe (fun _ _ _ _ hi => hi) worker hb

theorem runCryptWorkers_preserves : Preserves historyEvent RxHistory.runCryptWorkers :=
  PrefixPreserves.bind (schedule_preserves none) (fun _ => lift_quiet _)

theorem runSendWorkers_preserves : Preserves historyEvent RxHistory.runSendWorkers := by
  apply PrefixEnsures.preserves
  unfold RxHistory.runSendWorkers
  repeat' first
    | (audit_contract_head RxHistory.schedule; exact schedule_preserves _)
    | completion_env_steps

theorem afterXmit_preserves : Preserves historyEvent RxHistory.afterXmit := by
  apply PrefixEnsures.preserves
  unfold RxHistory.afterXmit
  repeat' first
    | (audit_contract_head RxHistory.runCryptWorkers; exact runCryptWorkers_preserves)
    | (audit_contract_head RxHistory.runSendWorkers; exact runSendWorkers_preserves)
    | completion_env_steps

theorem handshakeReceiveWorker_preserves : Preserves historyEvent RxHistory.handshakeReceiveWorker :=
  workerLoopPrefix_preserves _ _ closed_safe (origin_quiet _)
    (nestedResched_preserves _) _ _

theorem inject_preserves (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Preserves historyEvent (RxHistory.inject family port msg tos ll dest) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.inject
  repeat' first
    | (audit_contract_head RxHistory.runCryptWorkers; exact runCryptWorkers_preserves)
    | (audit_contract_head runWorkerPrefix; apply runWorker_preserves; apply PrefixEnsures.preserves)
    | completion_env_steps

theorem afterBatch_preserves : Preserves historyEvent RxHistory.afterBatch := by
  apply PrefixEnsures.preserves
  unfold RxHistory.afterBatch
  repeat' first
    | (audit_contract_head RxHistory.runCryptWorkers; exact runCryptWorkers_preserves)
    | (audit_contract_head RxHistory.runSendWorkers; exact runSendWorkers_preserves)
    | (audit_contract_head RxHistory.schedule; exact schedule_preserves _)
    | completion_env_steps

theorem flood_preserves (count port family : Nat) (messages : List (List UInt8)) :
    Preserves historyEvent (RxHistory.flood count port family messages) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.flood
  repeat' first
    | (audit_contract_head RxHistory.afterBatch; exact afterBatch_preserves)
    | (audit_contract_head RxHistory.pollScheduledInline; exact pollScheduledInline_preserves)
    | (audit_contract_head runWorkerPrefix; apply runWorker_preserves; apply PrefixEnsures.preserves)
    | completion_env_steps

theorem batchItem_preserves (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    Preserves historyEvent (RxHistory.batchItem d cqes item) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.batchItem
  repeat' first
    | (audit_contract_head RxHistory.pollScheduledInline; exact pollScheduledInline_preserves)
    | (audit_contract_head runWorkerPrefix; apply runWorker_preserves; apply PrefixEnsures.preserves)
    | completion_env_steps

theorem batch_preserves (items : List Env.BatchItem) : Preserves historyEvent (RxHistory.batch items) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.batch
  repeat' first
    | (audit_contract_head RxHistory.afterBatch; exact afterBatch_preserves)
    | (audit_contract_head RxHistory.batchItem; exact batchItem_preserves _ _ _)
    | completion_env_steps

theorem runTimers_preserves (jHi : UInt64) : Preserves historyEvent (RxHistory.runTimers jHi) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.runTimers
  repeat' first
    | (audit_contract_head RxHistory.runCryptWorkers; exact runCryptWorkers_preserves)
    | completion_env_steps

theorem runTimersPlaceholder_preserves (jHi : UInt64) :
    Preserves historyEvent (RxHistory.runTimersPlaceholder jHi) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.runTimersPlaceholder
  repeat' first
    | (audit_contract_head RxHistory.runCryptWorkers; exact runCryptWorkers_preserves)
    | (audit_contract_head RxHistory.runSendWorkers; exact runSendWorkers_preserves)
    | completion_env_steps

theorem idleTimers_preserves : Preserves historyEvent RxHistory.idleTimers := by
  apply PrefixEnsures.preserves
  unfold RxHistory.idleTimers
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | (audit_contract_head RxHistory.runTimers; exact runTimers_preserves _)
    | (audit_contract_head RxHistory.runTimersPlaceholder; exact runTimersPlaceholder_preserves _)
    | completion_env_steps

theorem afterAdvance_preserves : Preserves historyEvent RxHistory.afterAdvance := by
  apply PrefixEnsures.preserves
  unfold RxHistory.afterAdvance
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | (audit_contract_head RxHistory.runTimers; exact runTimers_preserves _)
    | (audit_contract_head RxHistory.runTimersPlaceholder; exact runTimersPlaceholder_preserves _)
    | completion_env_steps

theorem deferred_preserves (call : EnvDeferredCall) : Preserves historyEvent (RxHistory.deferred call) := by
  apply PrefixEnsures.preserves
  cases call with
  | drained what queues => exact audit_quiet _
  | idleDevice => exact audit_quiet _
  | noCrypt => exact audit_quiet _
  | crypt => exact runCryptWorkers_preserves
  | sendOne => exact audit_quiet _
  | clearOne => exact audit_quiet _
  | sendAll => exact runSendWorkers_preserves
  | afterXmit => exact afterXmit_preserves
  | timerWorker timer => exact audit_quiet _
  | timers jHi => exact runTimers_preserves jHi
  | placeholder jHi => exact runTimersPlaceholder_preserves jHi
  | idle => exact idleTimers_preserves
  | advance ticks => exact audit_quiet _
  | afterAdvance => exact afterAdvance_preserves


theorem observe_preserves : Preserves historyEvent RxHistory.observe :=
  PrefixPreserves.bind idleTimers_preserves (fun _ => lift_quiet _)

theorem remaining_preserves (call : EnvRemainingCall) : Preserves historyEvent (RxHistory.remaining call) := by
  apply PrefixEnsures.preserves
  cases call with
  | up => exact audit_quiet _
  | mtu value => exact audit_quiet _
  | route => exact audit_quiet _
  | down => exact audit_quiet _
  | delete => exact audit_quiet _
  | deladdr family => exact audit_quiet _
  | delroute family => exact audit_quiet _
  | observe => exact observe_preserves
  | inject family port msg tos ll dest => exact inject_preserves family port msg tos ll dest
  | flood count port family messages => exact flood_preserves count port family messages
  | inlinePoll => exact pollScheduledInline_preserves
  | afterBatch => exact afterBatch_preserves
  | batch items => exact batch_preserves items
  | cleanup => exact audit_quiet _
  | multicast family addr => exact audit_quiet _


theorem socketCallOn_preserves (fd : Nat) (body : RxHistory.Obs Int)
    (hb : Preserves historyEvent body) : Preserves historyEvent (RxHistory.socketCallOn fd body) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.socketCallOn
  repeat' first
    | exact hb
    | completion_env_steps

theorem syscallDispatch_preserves (call : Syscall) : Preserves historyEvent (RxHistory.syscallDispatch call) := by
  apply PrefixEnsures.preserves
  cases call
  case wgInject family port message tos ll dest =>
    exact socketCallOn_preserves _ _ (inject_preserves family port message tos ll dest)
  case wgFlood count port family messages => exact flood_preserves count port family messages
  case wgBatch items _ => exact batch_preserves items
  case wgObserve =>
    exact PrefixPreserves.bind observe_preserves (fun _ =>
      PrefixPreserves.bind (lift_quiet _) (fun _ =>
        socketCallOn_preserves _ _ (PrefixPreserves.pure closed_safe _)))
  all_goals exact audit_quiet _

/-- A normal negative errno reaches the same wait suffix as any other normal
return. A Stop keeps the already reached completion prefix and skips it. -/
theorem syscall_preserves (call : Syscall) : Preserves historyEvent (RxHistory.syscall call) := by
  apply PrefixEnsures.preserves
  unfold RxHistory.syscall
  repeat' first
    | contradiction
    | (audit_contract_head RxHistory.syscallDispatch; exact syscallDispatch_preserves _)
    | (audit_contract_head RxHistory.runSendWorkers; exact runSendWorkers_preserves)
    | (audit_contract_head RxHistory.idleTimers; exact idleTimers_preserves)
    | (audit_contract_head RxHistory.afterXmit; exact afterXmit_preserves)
    | (audit_contract_head RxHistory.afterAdvance; exact afterAdvance_preserves)
    | completion_env_steps

theorem syscallFamily_preserves (call : SyscallAuditCall) : Preserves historyEvent (RxHistory.syscallFamily call) := by
  apply PrefixEnsures.preserves
  cases call with
  | dispatch call => exact syscallDispatch_preserves call
  | syscall call => exact syscall_preserves call
  | netnsClose => exact audit_quiet _

end Leanux.Proofs.WG.Queues.RxCompletion
