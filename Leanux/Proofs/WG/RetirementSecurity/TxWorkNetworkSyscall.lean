import Leanux.Proofs.WG.RetirementSecurity.TxWorkControlDispatch

/-! The actual syscall entry and return tail for calls with no separately
filtered syscall number. Dispatch service is kept explicit here until its
native constructor family is joined; file cleanup and every deferred callback
are already concrete native contracts. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem current_task_suspension : TxSuspension.Keeps TaskM.getCurrent := by
  suspension_source [TaskM.getCurrent] using [TxSuspension.Nested.task_read]

theorem current_task_actor : Preserves (At (Covered locals crypt) crypt active) (getCurrent : Leanux.M Task) :=
  actor_task_via_fs current_task_suspension

theorem syscall_network_actor (call : Syscall) (number : syscallNr call=none)
    (dispatch_keeps : Preserves (At (Covered [] []) [] []) (dispatch call)) :
    Preserves (At (Covered [] []) [] []) (Leanux.syscall call) := by
  unfold Leanux.syscall
  rw [number]
  simp (config:={zeta:=false}) only [Env.windowTailCalls,List.forIn_nil,pure_bind]
  repeat' first
    | (rx_retention_head dispatch; exact dispatch_keeps)
    | (rx_retention_head getCurrent; exact current_task_actor)
    | (tx_file_lift FS.M; exact TxSuspension.Nested.task_work)
    | (rx_retention_head Env.runSendWorkers; exact send_workers_actor)
    | (rx_retention_head Env.idleTimers; exact idle_timers_actor)
    | (rx_retention_head Env.routeIntoWg0; exact route_into_actor)
    | (rx_retention_head Env.afterXmit; exact after_xmit_actor)
    | (rx_retention_head Env.afterAdvance; exact after_advance_actor)
    | (rx_retention_head Env.netnsCleanup; exact cleanup_actor)
    | (rx_retention_head _root_.modify
       apply hoare_modify
       intro w before
       exact before.store rfl rfl)
    | actor_control_step

end Leanux.Proofs.WG.RetirementSecurity.TxWork
