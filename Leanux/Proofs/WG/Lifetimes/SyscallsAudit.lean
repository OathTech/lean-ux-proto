import Leanux.Proofs.WG.Lifetimes.SyscallDispatchAudit

/-! Original syscall entry, dispatch and return-to-user work. The event state
stays outside Except, including failure during the post-dispatch worker/timer
wait. No parser, valid-descriptor, ownership, idle or drain premise is used.
This is the syscall boundary; initialized Runner composition remains separate. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
set_option maxHeartbeats 2000000
set_option pp.structureInstances false

def syscallAudit (call : Syscall) : AuditM Int := do
  liftPrefix (modify fun w => { w with steps := #[], userOut := none, userFds := none, extraOut := [], queuedThisCall := [], fired := #[], netRxSections := 0, netRxSection := 0, emitted := {}, translatedLen := none })
  -- seccomp: the entry path of the operation's own call once a mode is set
  -- (a harness call by design 6.2 rule 1: a cache hit); a probe enters itself
  match syscallNr call with
  | some nr => liftPrefix (Seccomp.enterHarnessCall nr)
  | none =>
    if call.isNet && (← liftPrefix getCurrent).seccomp.mode != .disabled then
      liftPrefix (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")
  let ret ← dispatchAudit call
  -- harness calls whose entry falls inside the window after the operation's (fixture knowledge)
  for c in Env.windowTailCalls do liftPrefix (Seccomp.enterHarnessCall c)
  liftPrefix taskWorkRun
  -- the guest waits inside the operations that can queue the handshake send
  -- worker (and in wg_inject); the worker runs during that wait
  -- worker; D3: a timer may fire in these waits (`idleTimersAudit`)
  match call with
  | .wgSet _ | .wgInject .. => runSendWorkersAudit; idleTimersAudit
  -- W9 (design 14.3b): the guest's route adds follow the up's wait
  | .wgUp => runSendWorkersAudit; idleTimersAudit; routeIntoWg0Audit
  | .wgXmit .. => afterXmitAudit; idleTimersAudit
  | .wgBatch .. => idleTimersAudit   -- W7: the batch runs its queued units itself
  -- D3: the guest waits after the advance; the next tick runs the due timers
  | .wgAdvance _ => afterAdvanceAudit
  -- W8: the namespace's teardown section runs in the guest's wait
  | .wgNetnsClose => envNetnsCleanupAudit
  | _ => pure ()
  return ret

macro "syscall_audit_erasure" : tactic => `(tactic|
  repeat' first
    | contradiction
    | with_reducible exact dispatchAudit_erases _
    | with_reducible exact runSendWorkersAudit_erases
    | with_reducible exact idleTimersAudit_erases
    | with_reducible exact routeIntoWg0Audit_erases
    | with_reducible exact afterXmitAudit_erases
    | with_reducible exact afterAdvanceAudit_erases
    | with_reducible exact envNetnsCleanupAudit_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

macro "syscall_audit_preservation" : tactic => `(tactic|
  repeat' first
    | contradiction
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
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

theorem syscallAudit_erases (call : Syscall) : ErasesPrefix (syscallAudit call) (syscall call) := by
  unfold syscallAudit syscall
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  syscall_audit_erasure

theorem syscallAudit_preserves (call : Syscall) : PrefixPreserves AuditInv AuditSafe (syscallAudit call) := by
  unfold syscallAudit
  try simp only [discard, map_const, Function.comp_def, map_eq_pure_bind, bind_assoc]
  syscall_audit_preservation

/-- The public dispatcher, complete syscall and fixture holder-close boundary.
All original Syscall constructors remain arguments, including arbitrary typed
values outside the parser's accepted input subset. -/
inductive SyscallAuditCall where
  | dispatch (call : Syscall)
  | syscall (call : Syscall)
  | netnsClose

namespace SyscallAuditCall

def original : SyscallAuditCall → M Int
  | .dispatch call => Leanux.dispatch call
  | .syscall call => Leanux.syscall call
  | .netnsClose => Leanux.netnsClose

def observed : SyscallAuditCall → AuditM Int
  | .dispatch call => dispatchAudit call
  | .syscall call => syscallAudit call
  | .netnsClose => netnsCloseAudit

theorem erases (call : SyscallAuditCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | dispatch call => exact dispatchAudit_erases call
  | syscall call => exact syscallAudit_erases call
  | netnsClose => exact netnsCloseAudit_erases

theorem preserves (call : SyscallAuditCall) : PrefixPreserves AuditInv AuditSafe call.observed := by
  cases call with
  | dispatch call => exact dispatchAudit_preserves call
  | syscall call => exact syscallAudit_preserves call
  | netnsClose => exact netnsCloseAudit_preserves

/-- Every actual saved filter entry derives its validity from the original
operation's local allocation-valid entry. The ordered filter equality includes
its Stops; safety of other candidate trials does not assert they executed. -/
theorem from_allocation (call : SyscallAuditCall) (w : World) (hi : AllocationInv [] w) :
    AuditSafe (runPrefix call.observed w []).2 ∧
    ∀ p ∈ probeEntries (runPrefix call.observed w []).2,
      AllocationInv p.history p.world ∧
      (p.world.suspended.filterM Env.Activation.consistent).run p.world =
        (p.world.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
          (fun ys => (ys, p.world)) ∧
      ∀ a ∈ p.world.suspended, LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 := by
  have hs := (call.preserves w [] (audit_initial hi)).choose_spec.2.1
  exact ⟨hs, fun p hp => savedProbe_trials hs.2 hp⟩

end SyscallAuditCall
end Leanux.Proofs.WG.Lifetimes
