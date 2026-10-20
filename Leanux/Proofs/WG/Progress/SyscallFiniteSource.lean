import Leanux.Proofs.WG.Progress.DispatchFiniteSource
import Leanux.Proofs.WG.Queues.JointSyscallLifecycle

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.SyscallFinite
open Leanux Leanux.WG
universe u

/-- Local variant of Configuration.syscallWith exposing the synchronous
task-work callback. All other entry/tail ordering is the shared factor's.
The original shared definition is unchanged. -/
def syscallWith_taskWork_variant {m : Type → Type u} [Monad m]
    (lift : {α : Type} → Leanux.M α → m α) (dispatch : m Int)
    (sendWorkers timers route xmit advance cleanup taskWork : m Unit) (call : Syscall) : m Int := do
  lift (modify fun w => { w with fs := {w.fs with userOut := none, userFds := none}, seccomp := {w.seccomp with emitted := {}, translatedLen := none} })
  lift (modifyWG fun g => {g with queuedThisCall := []})
  lift (modifyAmbient fun a => {a with steps := #[], extraOut := [], fired := #[], netRxSections := 0, netRxSection := 0})
  match syscallNr call with
  | some nr => lift (liftSeccomp (Seccomp.enterHarnessCall nr))
  | none =>
    if call.isNet && (← lift getCurrent).seccomp.mode != .disabled then
      lift (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")
  let ret ← dispatch
  for c in Env.windowTailCalls do lift (liftSeccomp (Seccomp.enterHarnessCall c))
  taskWork
  match call with
  | .wgSet _ | .wgInject .. => sendWorkers; timers
  | .wgUp => sendWorkers; timers; route
  | .wgXmit .. => xmit; timers
  | .wgBatch .. => timers   -- W7: the batch runs its queued units itself
  | .wgAdvance _ => advance
  | .wgNetnsClose => cleanup
  | _ => pure ()
  match call with
  | .wgUp | .wgDown | .wgDelete | .wgDeladdr _ | .wgDelroute .. | .wgSetMtu _ | .wgNetnsClose
  | .wgAddroute .. | .wgAddaddr .. =>
    let shape := Net.Fib.shape (← lift getRouting)
    lift (modifyAmbient fun w => {w with extraOut := w.extraOut ++ [("fib_trie", shape)]})
  | _ => pure ()
  return ret

theorem syscall_factor_taskWork_variant (c : Syscall) :
    Leanux.syscall c = syscallWith_taskWork_variant (fun {_} a => a)
      (Leanux.dispatch c) Env.runSendWorkers Env.idleTimers Env.routeIntoWg0
      Env.afterXmit Env.afterAdvance Env.netnsCleanup (liftFS Leanux.taskWorkRun) c := rfl

/-- Complete syscall with concrete finite dispatch, task-work and deferred
callbacks. Runtime filter entry and namespace cleanup are bounded native
walks; every original completion check and shape observation remains. -/
def call (c : Syscall) : Leanux.M Int :=
  syscallWith_taskWork_variant (fun {_} a => a) (DispatchFinite.call c)
    DeferredFinite.nativeSendAll DeferredFinite.nativeIdle Env.routeIntoWg0
    DeferredFinite.nativeAfterXmit DeferredFinite.nativeAfterAdvance Env.netnsCleanup
    (liftFS FsFinite.taskWorkRun) c

theorem call_source (c : Syscall) : Leanux.syscall c = call c := by
  rw [syscall_factor_taskWork_variant, DispatchFinite.call_source,
    DeferredFinite.nativeSendAll_source, DeferredFinite.nativeIdle_source,
    DeferredFinite.nativeAfterXmit_source, DeferredFinite.nativeAfterAdvance_source,
    FsFinite.taskWorkRun_source]
  rfl

end Leanux.Proofs.WG.Progress.SyscallFinite
