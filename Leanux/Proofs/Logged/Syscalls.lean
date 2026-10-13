import Leanux.Proofs.Logged.Operations
import Leanux.Syscalls

/-! The observed syscall uses the logged receive operations and original other
operations. Its erasure includes the entry reset and return-to-user work. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.Logged
open Leanux Leanux.WG Leanux.Env

def socketCallOnLogged (fd : Nat) (body : GhostM Int) : GhostM Int := do
  let f ← fdget fd
  -- W8: a closed fixture socket (the listeners after wg_netns_close):
  -- `fd_empty(f)` -> -EBADF (net/socket.c), before any socket layer runs
  if f.file.isNone then return -EBADF
  let ret ← body
  fdput f
  return ret

theorem socketCallOnLogged_erases (fd : Nat) (g : GhostM Int) (o : M Int)
    (h : Erases g o) : Erases (socketCallOnLogged fd g) (Leanux.socketCallOn fd o) := by
  unfold socketCallOnLogged Leanux.socketCallOn
  repeat' ghost_step

/-- Only these dispatch constructors can reach the receive-poll call chain.
Other dispatch cases retain the original whole action. -/
def dispatchLogged : Syscall → GhostM Int
  | .wgInject family port message tos ll dest =>
      socketCallOnLogged SENDER_FD (injectLogged family port message tos ll dest)
  | .wgFlood count port messages => floodLogged count port messages
  | .wgBatch items _ => batchLogged items
  | .wgObserve => do
    -- the fixture's observation happens whether or not the listener is still
    -- open (W8: after wg_netns_close the `recvfrom(4)` is -EBADF and the
    -- datagrams null, the sender's inbox and the stats are read as always)
    let (ret, observed) ← observeLogged
    modifyWorld fun w => { w with extraOut := ["datagrams", "replies", "stats"].map fun k => (k, observed.getObjValD k) }
    socketCallOn LISTEN4_FD (pure ret)
  | call => liftM (Leanux.dispatch call)

theorem dispatchLogged_erases (call : Syscall) : Erases (dispatchLogged call) (Leanux.dispatch call) := by
  cases call <;> simp only [dispatchLogged]
  all_goals first
    | with_reducible exact erases_liftM _
    | (simp only [Leanux.dispatch]
       repeat' first
         | with_reducible apply socketCallOnLogged_erases
         | with_reducible exact injectLogged_erases _ _ _ _ _ _
         | with_reducible exact floodLogged_erases _ _ _
         | with_reducible exact batchLogged_erases _
         | with_reducible exact observeLogged_erases
         | ghost_step)

def syscallLogged (call : Syscall) : GhostM Int := do
  modifyWorld fun w => { w with steps := #[], userOut := none, userFds := none, extraOut := [], queuedThisCall := [], fired := #[],
                                netRxSections := 0, netRxSection := 0, emitted := {}, translatedLen := none }
  match syscallNr call with
  | some nr => Seccomp.enterHarnessCall nr
  | none =>
    if call.isNet && (← getCurrent).seccomp.mode != .disabled then
      unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)"
  let ret ← dispatchLogged call
  for c in Env.windowTailCalls do Seccomp.enterHarnessCall c
  taskWorkRun
  -- the guest waits inside the operations that can queue the handshake send
  -- worker (and in wg_inject); the worker runs during that wait
  -- worker; D3: a timer may fire in these waits (`idleTimersLogged`)
  match call with
  | .wgSet _ | .wgInject .. => runSendWorkersLogged; idleTimersLogged
  -- W9 (design 14.3b): the guest's route adds follow the up's wait
  | .wgUp => runSendWorkersLogged; idleTimersLogged; Env.routeIntoWg0
  | .wgXmit .. => afterXmitLogged; idleTimersLogged
  | .wgBatch .. => idleTimersLogged   -- W7: the batch runs its queued units itself
  -- D3: the guest waits after the advance; the next tick runs the due timers
  | .wgAdvance _ => afterAdvanceLogged
  -- W8: the namespace's teardown section runs in the guest's wait
  | .wgNetnsClose => Env.netnsCleanup
  | _ => pure ()
  return ret

theorem syscallLogged_erases (call : Syscall) : Erases (syscallLogged call) (Leanux.syscall call) := by
  unfold syscallLogged Leanux.syscall
  repeat' first
    | with_reducible exact dispatchLogged_erases _
    | with_reducible exact runSendWorkersLogged_erases
    | with_reducible exact idleTimersLogged_erases
    | with_reducible exact afterXmitLogged_erases
    | with_reducible exact afterAdvanceLogged_erases
    | ghost_step

end Leanux.Proofs.Logged
