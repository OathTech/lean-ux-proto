import Leanux.Proofs.WG.Queues.RxLinkCallers
import Leanux.Proofs.WG.Queues.RxSyscallsHistory

/-! Linkage and receipt truth through the existing environment and syscall observers.
Every exact flood producer, inline batch polls, recorded/placeholder timer suffixes and
normal negative syscall returns retain their concrete callback continuations. -/
namespace Leanux.Proofs.WG.Queues.RxLink
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

variable {P : List RxHistory.Event → Prop} [Protocol P]

theorem runWorker_preserves (worker : Worker) (body : RxHistory.Obs Unit)
    (hb : Preserves P body) : Preserves P (runWorkerPrefix worker body) :=
  runWorkerPrefix_preserves history_safe (fun _ _ _ _ hi => hi) worker hb

theorem runCryptWorkers_preserves : Preserves P RxHistory.runCryptWorkers :=
  PrefixPreserves.bind (schedule_preserves none) (fun _ => lift_quiet _)

theorem runSendWorkers_preserves : Preserves P RxHistory.runSendWorkers := by
  unfold RxHistory.runSendWorkers
  repeat' first
    | with_reducible exact schedule_preserves _
    | link_steps

theorem afterXmit_preserves : Preserves P RxHistory.afterXmit := by
  unfold RxHistory.afterXmit
  repeat' first
    | with_reducible exact runCryptWorkers_preserves
    | with_reducible exact runSendWorkers_preserves
    | link_steps

theorem handshakeReceiveWorker_preserves : Preserves P RxHistory.handshakeReceiveWorker :=
  workerLoopPrefix_preserves _ _ history_safe (mixed_quiet _)
    (nestedResched_preserves _) _ _

theorem inject_preserves (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Preserves P (RxHistory.inject family port msg tos ll dest) := by
  unfold RxHistory.inject
  repeat' first
    | with_reducible exact runCryptWorkers_preserves
    | with_reducible apply runWorker_preserves
    | link_steps

theorem afterBatch_preserves : Preserves P RxHistory.afterBatch := by
  unfold RxHistory.afterBatch
  repeat' first
    | with_reducible exact runCryptWorkers_preserves
    | with_reducible exact runSendWorkers_preserves
    | with_reducible exact schedule_preserves _
    | link_steps

theorem flood_preserves (count port family : Nat) (messages : List (List UInt8)) :
    Preserves P (RxHistory.flood count port family messages) := by
  unfold RxHistory.flood
  repeat' first
    | with_reducible exact afterBatch_preserves
    | with_reducible exact pollScheduledInline_preserves
    | with_reducible apply runWorker_preserves
    | link_steps

theorem batchItem_preserves (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    Preserves P (RxHistory.batchItem d cqes item) := by
  unfold RxHistory.batchItem
  repeat' first
    | with_reducible exact pollScheduledInline_preserves
    | with_reducible apply runWorker_preserves
    | link_steps

theorem batch_preserves (items : List Env.BatchItem) : Preserves P (RxHistory.batch items) := by
  unfold RxHistory.batch
  repeat' first
    | with_reducible exact afterBatch_preserves
    | with_reducible exact batchItem_preserves _ _ _
    | link_steps

theorem runTimers_preserves (jHi : UInt64) : Preserves P (RxHistory.runTimers jHi) := by
  unfold RxHistory.runTimers
  repeat' first
    | with_reducible exact runCryptWorkers_preserves
    | link_steps

theorem runTimersPlaceholder_preserves (jHi : UInt64) :
    Preserves P (RxHistory.runTimersPlaceholder jHi) := by
  unfold RxHistory.runTimersPlaceholder
  repeat' first
    | with_reducible exact runCryptWorkers_preserves
    | with_reducible exact runSendWorkers_preserves
    | link_steps

theorem idleTimers_preserves : Preserves P RxHistory.idleTimers := by
  unfold RxHistory.idleTimers
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact runTimers_preserves _
    | link_steps

theorem afterAdvance_preserves : Preserves P RxHistory.afterAdvance := by
  unfold RxHistory.afterAdvance
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact runTimers_preserves _
    | with_reducible exact runTimersPlaceholder_preserves _
    | link_steps

theorem deferred_preserves (call : EnvDeferredCall) : Preserves P (RxHistory.deferred call) := by
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
  | fire worker jHi => exact audit_quiet _
  | timers jHi => exact runTimers_preserves jHi
  | placeholder jHi => exact runTimersPlaceholder_preserves jHi
  | idle => exact idleTimers_preserves
  | advance ticks => exact audit_quiet _
  | afterAdvance => exact afterAdvance_preserves


theorem observe_preserves : Preserves P RxHistory.observe :=
  PrefixPreserves.bind idleTimers_preserves (fun _ => lift_quiet _)

theorem remaining_preserves (call : EnvRemainingCall) : Preserves P (RxHistory.remaining call) := by
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
    (hb : Preserves P body) : Preserves P (RxHistory.socketCallOn fd body) := by
  unfold RxHistory.socketCallOn
  repeat' first
    | exact hb
    | link_steps

theorem syscallDispatch_preserves (call : Syscall) : Preserves P (RxHistory.syscallDispatch call) := by
  cases call
  case wgInject family port message tos ll dest =>
    exact socketCallOn_preserves _ _ (inject_preserves family port message tos ll dest)
  case wgFlood count port family messages => exact flood_preserves count port family messages
  case wgBatch items _ => exact batch_preserves items
  case wgObserve =>
    exact PrefixPreserves.bind observe_preserves (fun _ =>
      PrefixPreserves.bind (lift_quiet _) (fun _ =>
        socketCallOn_preserves _ _ (PrefixPreserves.pure history_safe _)))
  all_goals exact audit_quiet _

/-- A normal negative errno reaches the same wait suffix as any other normal
return. A Stop keeps the already reached linked/valid prefix and skips it. -/
theorem syscall_preserves (call : Syscall) : Preserves P (RxHistory.syscall call) := by
  unfold RxHistory.syscall
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | contradiction
    | with_reducible exact syscallDispatch_preserves _
    | with_reducible exact runSendWorkers_preserves
    | with_reducible exact idleTimers_preserves
    | with_reducible exact afterXmit_preserves
    | with_reducible exact afterAdvance_preserves
    | link_steps

theorem syscallFamily_preserves (call : SyscallAuditCall) : Preserves P (RxHistory.syscallFamily call) := by
  cases call with
  | dispatch call => exact syscallDispatch_preserves call
  | syscall call => exact syscall_preserves call
  | netnsClose => exact audit_quiet _

end Leanux.Proofs.WG.Queues.RxLink
