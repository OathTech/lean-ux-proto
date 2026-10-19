import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerFactor

/-! Fixed syscall entry and suffix bodies expose the actual reset and
seccomp guard before dispatch. Their factor keeps every original tail call. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SyscallSource
open Leanux Leanux.WG Leanux.Proofs.Logged Queues Configuration TransmitSecurity
open CausalJournal

def enter (call : Syscall) : PrefixM CausalJournal.Event Unit := do
  liftPrefix (modify fun w => {w with fs := {w.fs with userOut := none,userFds := none}, seccomp := {w.seccomp with emitted := {},translatedLen := none}})
  liftPrefix (modifyWG fun g=>{g with queuedThisCall:=[]})
  liftPrefix (modifyAmbient fun a=>{a with steps:=#[],extraOut:=[],fired:=#[],netRxSections:=0,netRxSection:=0})
  match syscallNr call with
  | some nr=>liftPrefix (liftSeccomp (Seccomp.enterHarnessCall nr))
  | none=>
    if call.isNet && (←liftPrefix getCurrent).seccomp.mode != .disabled then
      liftPrefix (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")

def afterDispatch (call : Syscall) (ret : Int) : PrefixM Event Int := do
  for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
  liftPrefix (liftFS taskWorkRun)
  match call with
  | .wgSet _ | .wgInject .. => Driver.sendWorkersObserved hooks; Driver.idleTimersObserved hooks
  | .wgUp => Driver.sendWorkersObserved hooks; Driver.idleTimersObserved hooks; liftPrefix Env.routeIntoWg0
  | .wgXmit .. => Driver.afterXmitObserved hooks; Driver.idleTimersObserved hooks
  | .wgBatch .. => Driver.idleTimersObserved hooks
  | .wgAdvance _ => Driver.afterAdvanceObserved hooks
  | .wgNetnsClose => liftPrefix Env.netnsCleanup
  | _ => pure ()
  match call with
  | .wgUp | .wgDown | .wgDelete | .wgDeladdr _ | .wgDelroute .. | .wgSetMtu _ | .wgNetnsClose
  | .wgAddroute .. | .wgAddaddr .. =>
    let shape := Net.Fib.shape (← liftPrefix getRouting)
    liftPrefix (modifyAmbient fun w=>{w with extraOut:=w.extraOut++[("fib_trie",shape)]})
  | _ => pure ()
  return ret

def afterEntry (call : Syscall) : PrefixM Event Int := do
  let ret ← Driver.dispatchObserved hooks call
  afterDispatch call ret

/-- This fixed factor retains the original syscall's exact native prefix,
including entry failures before any dispatch occurs. -/
theorem syscall_factor (call : Syscall) :
    Driver.syscallObserved hooks call = (enter call >>= fun _=>afterEntry call) := by
  unfold Driver.syscallObserved syscallWith enter afterEntry afterDispatch
  cases syscallNr call
  · simp only [bind_assoc]
    congr 1
    funext ignored
    congr 1
    funext ignored
    congr 1
    funext ignored
    congr 1
    funext task
    split <;> rfl
  · simp only [bind_assoc]
    rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SyscallSource
