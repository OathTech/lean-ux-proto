import Leanux.Proofs.WG.Queues.RxSyscallDispatchHistory

/-! Original syscall entry and all return-to-user continuations. Normal errno
returns still run their source-designated worker/timer suffix. A Stop keeps the
reached history; bookkeeping resets never reset the persistent observer journal. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def syscall (call : Syscall) : Obs Int := do
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
  let ret ← syscallDispatch call
  -- harness calls whose entry falls inside the window after the operation's (fixture knowledge)
  for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
  liftPrefix (liftFS taskWorkRun)
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
  match call with
  | .wgUp | .wgDown | .wgDelete | .wgDeladdr _ | .wgDelroute .. | .wgSetMtu _ | .wgNetnsClose
  | .wgAddroute .. | .wgAddaddr .. =>
    let shape := Net.Fib.shape (← liftPrefix getRouting)
    liftPrefix (modifyAmbient fun w => {w with extraOut := w.extraOut ++ [("fib_trie", shape)]})
  | _ => pure ()
  return ret
macro "rx_syscall_lower" : tactic => `(tactic|
  first
    | (audit_contract_head getCurrent; apply auditLift_store;
        intro initial; unfold Leanux.getCurrent;
        change Hoare (liftFS (StateT.lift TaskM.getCurrent)) _ _;
        exact productFS_spec (StateT.lift TaskM.getCurrent)
          (fun w => wgStoreView w.wg = initial) (fun _ _ _ _ hi => hi))
    | (audit_contract_head dispatchAudit; exact dispatchAudit_preserves _)
    | (audit_contract_head runSendWorkersAudit; exact runSendWorkersAudit_preserves)
    | (audit_contract_head idleTimersAudit; exact idleTimersAudit_preserves)
    | (audit_contract_head routeIntoWg0Audit; exact routeIntoWg0Audit_preserves)
    | (audit_contract_head afterXmitAudit; exact afterXmitAudit_preserves)
    | (audit_contract_head afterAdvanceAudit; exact afterAdvanceAudit_preserves)
    | (audit_contract_head envNetnsCleanupAudit; exact envNetnsCleanupAudit_preserves)
    | (control_audit_routing; exact auditLift_store _ (by
        intro initial; exact productRouting_spec _ (fun s => s.2.2.2 = initial)))
    | syscall_audit_component
    | control_audit_preserves)

macro "rx_syscall_erasure" : tactic => `(tactic|
  first
    | (rx_env_traffic_head syscallDispatch; exact syscallDispatch_erases _)
    | (rx_env_traffic_head idleTimers; exact idleTimers_erases)
    | (rx_env_traffic_head routeIntoWg0Audit; exact audit_erases routeIntoWg0Audit_erases)
    | (rx_env_traffic_head afterXmit; exact afterXmit_erases)
    | (rx_env_traffic_head afterAdvance; exact afterAdvance_erases)
    | (rx_env_traffic_head envNetnsCleanupAudit; exact audit_erases envNetnsCleanupAudit_erases)
    | rx_env_traffic_erasure)

macro "rx_syscall_preservation" : tactic => `(tactic|
  first
    | (rx_env_traffic_head syscallDispatch; exact syscallDispatch_preserves _)
    | (rx_env_traffic_head idleTimers; exact idleTimers_preserves)
    | (rx_env_traffic_head routeIntoWg0Audit; exact audit_preserves _ routeIntoWg0Audit_preserves)
    | (rx_env_traffic_head afterXmit; exact afterXmit_preserves)
    | (rx_env_traffic_head afterAdvance; exact afterAdvance_preserves)
    | (rx_env_traffic_head envNetnsCleanupAudit; exact audit_preserves _ envNetnsCleanupAudit_preserves)
    | (rx_env_traffic_head liftPrefix; apply boundaryLift_audit; rx_syscall_lower)
    | rx_env_traffic_preservation)

macro "rx_syscall_projection" : tactic => `(tactic|
  first
    | (audit_contract ProjectsUnder; first
        | (rx_env_traffic_head syscallDispatch; exact syscallDispatch_projects _)
        | (rx_env_traffic_head idleTimers; exact idleTimers_projects)
        | (rx_env_traffic_head routeIntoWg0Audit; exact audit_projects routeIntoWg0Audit_preserves)
        | (rx_env_traffic_head afterXmit; exact afterXmit_projects)
        | (rx_env_traffic_head afterAdvance; exact afterAdvance_projects)
        | (rx_env_traffic_head envNetnsCleanupAudit; exact audit_projects envNetnsCleanupAudit_preserves))
    | (audit_contract PrefixPreserves; rx_syscall_lower)
    | (audit_contract PrefixEnsures; rx_syscall_lower)
    | rx_env_traffic_projection)

theorem syscall_erases (call : Syscall) : ErasesPrefix (syscall call) (Leanux.syscall call) := by
  unfold syscall Leanux.syscall
  repeat' rx_syscall_erasure
  all_goals contradiction

theorem syscall_preserves (call : Syscall) : PrefixPreserves BoundaryInv BoundarySafe (syscall call) := by
  unfold syscall
  repeat' rx_syscall_preservation

/-- The actual return-to-user suffix is checked independently of the entry
matcher, without changing the observer or assuming a successful dispatch. -/
private theorem syscall_tail_projects (call : Syscall) (ret : Int) :
    ProjectsUnder AuditInv auditEvent (do
      for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
      liftPrefix (liftFS taskWorkRun)
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
      match call with
      | .wgUp | .wgDown | .wgDelete | .wgDeladdr _ | .wgDelroute .. | .wgSetMtu _ | .wgNetnsClose
      | .wgAddroute .. | .wgAddaddr .. =>
        let shape := Net.Fib.shape (← liftPrefix getRouting)
        liftPrefix (modifyAmbient fun w => {w with extraOut := w.extraOut ++ [("fib_trie", shape)]})
      | _ => pure ()
      return ret
    : Obs Int) (do
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
    : AuditM Int) := by
  cases call <;> repeat' rx_syscall_projection

/-- The entry path transports any exact continuation; its action domain remains
the real product observer, including every seccomp failure. -/
private theorem syscall_entry_projects {α : Type} (call : Syscall)
    (g : Obs α) (a : AuditM α) (hg : ProjectsUnder AuditInv auditEvent g a) :
    ProjectsUnder AuditInv auditEvent (do
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
    g : Obs α) (do
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
    a : AuditM α) := by
  repeat' rx_syscall_projection
  all_goals exact hg

theorem syscall_projects (call : Syscall) :
    ProjectsUnder AuditInv auditEvent (syscall call) (syscallAudit call) := by
  unfold syscall syscallAudit
  apply syscall_entry_projects call
  exact projectsUnder_bind (syscallDispatch_projects call)
    (dispatchAudit_preserves call) (fun ret => syscall_tail_projects call ret)

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
