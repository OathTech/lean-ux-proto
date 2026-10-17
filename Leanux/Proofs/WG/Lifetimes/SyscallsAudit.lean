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
  liftPrefix (modify fun w => { w with fs := {w.fs with userOut := none, userFds := none}, seccomp := {w.seccomp with emitted := {}, translatedLen := none} })
  liftPrefix (modifyWG fun g => {g with queuedThisCall := []})
  liftPrefix (modifyAmbient fun a => {a with steps := #[], extraOut := [], fired := #[], netRxSections := 0, netRxSection := 0})
  -- seccomp: the entry path of the operation's own call once a mode is set
  -- (a harness call by design 6.2 rule 1: a cache hit); a probe enters itself
  match syscallNr call with
  | some nr => liftPrefix (liftSeccomp (Seccomp.enterHarnessCall nr))
  | none =>
    if call.isNet && (← liftPrefix getCurrent).seccomp.mode != .disabled then
      liftPrefix (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")
  let ret ← dispatchAudit call
  -- harness calls whose entry falls inside the window after the operation's (fixture knowledge)
  for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
  liftPrefix (liftFS taskWorkRun)
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
  match call with
  | .wgUp | .wgDown | .wgDelete | .wgDeladdr _ | .wgDelroute .. | .wgSetMtu _ | .wgNetnsClose
  | .wgAddroute .. | .wgAddaddr .. =>
    let shape := Net.Fib.shape (← liftPrefix getRouting)
    liftPrefix (modifyAmbient fun w => {w with extraOut := w.extraOut ++ [("fib_trie", shape)]})
  | _ => pure ()
  return ret

macro "syscall_audit_erasure" : tactic => `(tactic|
  repeat' first
    | (maintenance_head dispatchAudit; exact dispatchAudit_erases _)
    | (maintenance_head runSendWorkersAudit; exact runSendWorkersAudit_erases )
    | (maintenance_head idleTimersAudit; exact idleTimersAudit_erases )
    | (maintenance_head routeIntoWg0Audit; exact routeIntoWg0Audit_erases )
    | (maintenance_head afterXmitAudit; exact afterXmitAudit_erases )
    | (maintenance_head afterAdvanceAudit; exact afterAdvanceAudit_erases )
    | (maintenance_head envNetnsCleanupAudit; exact envNetnsCleanupAudit_erases )
    | (maintenance_head ForIn.forIn; apply erasesPrefix_forIn)
    | control_audit_erases)

macro "syscall_audit_preservation" : tactic => `(tactic|
  repeat' first
    | (audit_contract_head dispatchAudit; exact dispatchAudit_preserves _)
    | (audit_contract_head runSendWorkersAudit; exact runSendWorkersAudit_preserves )
    | (audit_contract_head idleTimersAudit; exact idleTimersAudit_preserves )
    | (audit_contract_head routeIntoWg0Audit; exact routeIntoWg0Audit_preserves )
    | (audit_contract_head afterXmitAudit; exact afterXmitAudit_preserves )
    | (audit_contract_head afterAdvanceAudit; exact afterAdvanceAudit_preserves )
    | (audit_contract_head envNetnsCleanupAudit; exact envNetnsCleanupAudit_preserves )
    | (audit_contract_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe))
    | (control_audit_routing; exact auditLift_store _ (by intro initial; exact productRouting_spec _ (fun s => s.2.2.2 = initial)))
    | syscall_audit_component
    | control_audit_preserves)

theorem syscallAudit_erases (call : Syscall) : ErasesPrefix (syscallAudit call) (syscall call) := by
  unfold syscallAudit syscall
  syscall_audit_erasure

theorem syscallAudit_preserves (call : Syscall) : PrefixPreserves AuditInv AuditSafe (syscallAudit call) := by
  apply PrefixEnsures.preserves
  unfold syscallAudit
  syscall_audit_preservation
  all_goals
    apply auditLift_store
    intro initial
    unfold Leanux.getCurrent
    change Hoare (liftFS (StateT.lift TaskM.getCurrent)) _ _
    exact productFS_spec (StateT.lift TaskM.getCurrent)
      (fun w => wgStoreView w.wg = initial) (fun _ _ _ _ hi => hi)

/-- The public dispatcher, complete syscall and fixture holder-close boundary.
All original Syscall constructors remain arguments, including arbitrary typed
values outside the parser's accepted input subset. -/
inductive SyscallAuditCall where
  | dispatch (call : Syscall)
  | syscall (call : Syscall)
  | netnsClose

namespace SyscallAuditCall

def original : SyscallAuditCall → Leanux.M Int
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
theorem from_allocation (call : SyscallAuditCall) (w : World) (hi : AllocationInv [] w.wg) :
    AuditSafe (runPrefix call.observed w []).2 ∧
    ∀ p ∈ probeEntries (runPrefix call.observed w []).2,
      AllocationInv p.history p.world.wg ∧
      (p.world.ambient.suspended.filterM Env.Activation.consistent).run p.world =
        (p.world.ambient.suspended.filterM (fun a => activationTrialDecision a p.world p.history)).map
          (fun ys => (ys, p.world)) ∧
      ∀ a ∈ p.world.ambient.suspended, LifetimeEvent.Safe (runPrefix (activationRunPrefix a) p.world p.history).2 := by
  have hs := (call.preserves w [] (audit_initial hi)).choose_spec.2.1
  exact ⟨hs, fun p hp => savedProbe_trials hs.2 hp⟩

end SyscallAuditCall
end Leanux.Proofs.WG.Lifetimes
