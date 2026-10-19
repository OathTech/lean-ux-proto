import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReturnEntry

/-! Literal return-to-user callback order, after the original dispatch and
before the routing observation. Numeric prefixes keep repeated callback values
at their original positions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReturnSource
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity CausalJournal

def prelude : PrefixM Event Unit := do
  for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
  liftPrefix (liftFS taskWorkRun)

def callbacks : Syscall → List (PrefixM Event Unit)
  | .wgSet _ | .wgInject .. => [Driver.sendWorkersObserved hooks,Driver.idleTimersObserved hooks]
  | .wgUp => [Driver.sendWorkersObserved hooks,Driver.idleTimersObserved hooks,liftPrefix Env.routeIntoWg0]
  | .wgXmit .. => [Driver.afterXmitObserved hooks,Driver.idleTimersObserved hooks]
  | .wgBatch .. => [Driver.idleTimersObserved hooks]
  | .wgAdvance _ => [Driver.afterAdvanceObserved hooks]
  | .wgNetnsClose => [liftPrefix Env.netnsCleanup]
  | _ => []

def sequence : List (PrefixM Event Unit) → PrefixM Event Unit
  | [] => pure ()
  | action::rest => action >>= fun _=>sequence rest

def routing : Syscall → PrefixM Event Unit
  | .wgUp | .wgDown | .wgDelete | .wgDeladdr _ | .wgDelroute .. | .wgSetMtu _ | .wgNetnsClose
  | .wgAddroute .. | .wgAddaddr .. => do
    let shape := Net.Fib.shape (← liftPrefix getRouting)
    liftPrefix (modifyAmbient fun w=>{w with extraOut:=w.extraOut++[("fib_trie",shape)]})
  | _ => pure ()

theorem sequence_append (front rest : List (PrefixM Event Unit)) :
    sequence (front++rest)=(sequence front >>= fun _=>sequence rest) := by
  induction front with
  | nil => simp only [List.nil_append,sequence,pure_bind]
  | cons action front ih => simp only [List.cons_append,sequence,ih,bind_assoc]

theorem after_dispatch_factor (call : Syscall) (ret : Int) :
    SyscallSource.afterDispatch call ret = (do
      prelude
      sequence (callbacks call)
      routing call
      pure ret) := by
  cases call <;> simp only [SyscallSource.afterDispatch,prelude,callbacks,sequence,
    routing,bind_assoc,pure_bind]

def callbackPrefix (call : Syscall) (count : Nat) : PrefixM Event Unit := do
  prelude
  sequence ((callbacks call).take count)

def callbackSuffix (call : Syscall) (count : Nat) (ret : Int) : PrefixM Event Int := do
  sequence ((callbacks call).drop count)
  routing call
  pure ret

theorem callback_factor (call : Syscall) (ret : Int) (count : Nat) :
    SyscallSource.afterDispatch call ret =
      (callbackPrefix call count >>= fun _=>callbackSuffix call count ret) := by
  rw [after_dispatch_factor]
  have ordered := sequence_append ((callbacks call).take count) ((callbacks call).drop count)
  rw [List.take_append_drop] at ordered
  simp only [callbackPrefix,callbackSuffix,ordered,bind_assoc]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ReturnSource
