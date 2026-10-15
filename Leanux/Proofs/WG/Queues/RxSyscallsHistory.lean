import Leanux.Proofs.WG.Queues.RxSyscallDispatchHistory

/-! Original syscall entry and all return-to-user continuations. Normal errno
returns still run their source-designated worker/timer suffix. A Stop keeps the
reached history; bookkeeping resets never reset the persistent observer journal. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def syscall (call : Syscall) : Obs Int := do
  liftPrefix (modify fun w => { w with steps := #[], userOut := none, userFds := none, extraOut := [], queuedThisCall := [], fired := #[], netRxSections := 0, netRxSection := 0, emitted := {}, translatedLen := none })
  -- seccomp: the entry path of the operation's own call once a mode is set
  -- (a harness call by design 6.2 rule 1: a cache hit); a probe enters itself
  match syscallNr call with
  | some nr => liftPrefix (Seccomp.enterHarnessCall nr)
  | none =>
    if call.isNet && (← liftPrefix getCurrent).seccomp.mode != .disabled then
      liftPrefix (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")
  let ret ← syscallDispatch call
  -- harness calls whose entry falls inside the window after the operation's (fixture knowledge)
  for c in Env.windowTailCalls do liftPrefix (Seccomp.enterHarnessCall c)
  liftPrefix taskWorkRun
  -- the guest waits inside the operations that can queue the handshake send
  -- worker (and in wg_inject); the worker runs during that wait
  -- worker; D3: a timer may fire in these waits (`idleTimers`)
  match call with
  | .wgSet _ | .wgInject .. => runSendWorkers; idleTimers
  -- W9 (design 14.3b): the guest's route adds follow the up's wait
  | .wgUp => runSendWorkers; idleTimers; (audit routeIntoWg0Audit)
  | .wgXmit .. => afterXmit; idleTimers
  | .wgBatch .. => idleTimers   -- W7: the batch runs its queued units itself
  -- D3: the guest waits after the advance; the next tick runs the due timers
  | .wgAdvance _ => afterAdvance
  -- W8: the namespace's teardown section runs in the guest's wait
  | .wgNetnsClose => (audit envNetnsCleanupAudit)
  | _ => pure ()
  return ret

theorem syscall_erases (call : Syscall) : ErasesPrefix (syscall call) (Leanux.syscall call) := by
  unfold syscall Leanux.syscall
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | contradiction
    | with_reducible exact syscallDispatch_erases _
    | with_reducible exact runSendWorkers_erases
    | with_reducible exact idleTimers_erases
    | with_reducible exact audit_erases routeIntoWg0Audit_erases
    | with_reducible exact afterXmit_erases
    | with_reducible exact afterAdvance_erases
    | with_reducible exact audit_erases envNetnsCleanupAudit_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split <;> try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem syscall_preserves (call : Syscall) : PrefixPreserves BoundaryInv BoundarySafe (syscall call) := by
  unfold syscall
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | contradiction
    | with_reducible exact syscallDispatch_preserves _
    | with_reducible exact runSendWorkers_preserves
    | with_reducible exact idleTimers_preserves
    | with_reducible exact audit_preserves _ routeIntoWg0Audit_preserves
    | with_reducible exact afterXmit_preserves
    | with_reducible exact afterAdvance_preserves
    | with_reducible exact audit_preserves _ envNetnsCleanupAudit_preserves
    | with_reducible exact boundaryLift_audit _ (auditLift_wgKernel _ (SeccompFrames.enterHarnessCall_sameWGKernel _))
    | with_reducible exact boundaryLift_audit _ (auditLift_wgKernel _ SignalFrames.getCurrent_sameWGKernel)
    | with_reducible exact boundaryLift_audit _ (auditLift_wgKernel _ FSFrames.taskWorkRun_sameWGKernel)
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split <;> try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem syscall_projects (call : Syscall) :
    ProjectsUnder AuditInv auditEvent (syscall call) (syscallAudit call) := by
  unfold syscall syscallAudit
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  repeat' first
    | contradiction
    | with_reducible exact syscallDispatch_projects _
    | with_reducible exact runSendWorkers_projects
    | with_reducible exact idleTimers_projects
    | with_reducible exact audit_projects routeIntoWg0Audit_preserves
    | with_reducible exact afterXmit_projects
    | with_reducible exact afterAdvance_projects
    | with_reducible exact audit_projects envNetnsCleanupAudit_preserves
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible exact dispatchAudit_preserves _
    | with_reducible exact runSendWorkersAudit_preserves
    | with_reducible exact idleTimersAudit_preserves
    | with_reducible exact routeIntoWg0Audit_preserves
    | with_reducible exact afterXmitAudit_preserves
    | with_reducible exact afterAdvanceAudit_preserves
    | with_reducible exact envNetnsCleanupAudit_preserves
    | with_reducible exact auditLift_wgKernel _ (SeccompFrames.enterHarnessCall_sameWGKernel _)
    | with_reducible exact auditLift_wgKernel _ SignalFrames.getCurrent_sameWGKernel
    | with_reducible exact auditLift_wgKernel _ FSFrames.taskWorkRun_sameWGKernel
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply projectsUnder_forIn
    | with_reducible apply projectsUnder_bind
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

/-- Complete original public call family; no hidden poll is whole-call focused. -/
def syscallFamily : SyscallAuditCall → Obs Int
  | .dispatch call => syscallDispatch call
  | .syscall call => syscall call
  | .netnsClose => audit netnsCloseAudit

theorem syscallFamily_erases (call : SyscallAuditCall) :
    ErasesPrefix (syscallFamily call) call.original := by
  cases call with
  | dispatch call => exact syscallDispatch_erases call
  | syscall call => exact syscall_erases call
  | netnsClose => exact audit_erases netnsCloseAudit_erases

theorem syscallFamily_preserves (call : SyscallAuditCall) :
    PrefixPreserves BoundaryInv BoundarySafe (syscallFamily call) := by
  cases call with
  | dispatch call => exact syscallDispatch_preserves call
  | syscall call => exact syscall_preserves call
  | netnsClose => exact audit_preserves _ netnsCloseAudit_preserves

theorem syscallFamily_projects (call : SyscallAuditCall) :
    ProjectsUnder AuditInv auditEvent (syscallFamily call) call.observed := by
  cases call with
  | dispatch call => exact syscallDispatch_projects call
  | syscall call => exact syscall_projects call
  | netnsClose => exact audit_projects netnsCloseAudit_preserves

end Leanux.Proofs.WG.Queues.RxHistory
