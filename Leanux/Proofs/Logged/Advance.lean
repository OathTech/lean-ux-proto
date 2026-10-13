import Leanux.Proofs.Logged.TimerPass
import Leanux.Syscalls

/-! The original advance syscall prefix and its timer wait. This boundary
retains descriptor, seccomp and return-to-user effects before observing timers. -/
namespace Leanux.Proofs.Logged
open Leanux Leanux.Env

def advancePrelude (ticks : Nat) : M Int := do
  modify fun w => { w with steps := #[], userOut := none, userFds := none, extraOut := [], queuedThisCall := [], fired := #[],
                           netRxSections := 0, netRxSection := 0, emitted := {}, translatedLen := none }
  match syscallNr (.wgAdvance ticks) with
  | some nr => Seccomp.enterHarnessCall nr
  | none =>
    if (Syscall.wgAdvance ticks).isNet && (← getCurrent).seccomp.mode != .disabled then
      unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)"
  let ret ← dispatch (.wgAdvance ticks)
  for c in windowTailCalls do Seccomp.enterHarnessCall c
  taskWorkRun
  return ret

theorem syscallAdvance_factor (ticks : Nat) :
    syscall (.wgAdvance ticks) = (do
      let ret ← advancePrelude ticks
      afterAdvance
      return ret) := by
  simp only [syscall, advancePrelude, syscallNr, Syscall.isNet, Bool.true_and,
    bind_assoc]
  congr 1
  funext u
  congr 1
  funext p
  split <;> simp only [bind_assoc, pure_bind]

private theorem map_erases (f : α → β) {g : PrefixM Event α} {a : M α}
    (h : ErasesPrefix g a) : ErasesPrefix (f <$> g) (f <$> a) := by
  simpa only [bind_pure_comp] using erasesPrefix_bind h (fun x => erasesPrefix_pure (f x))

def afterAdvanceObserved : PrefixM TimerObservation Unit := do
  let w ← liftPrefix (get : M World)
  if w.hidden.isNone then
    let jHi := w.jiffiesLast.getD 0 + w.timing.advanceWait.toUInt64
    if w.hiddenPlaceholders then liftPrefix (runTimersPlaceholder jHi)
    else discard <| timerPassObserved jHi
    return
  let some jEnd ← liftPrefix (peekSiteU64 .jiffiesEnd)
    | liftPrefix <| throw (.hidden "no end-of-wait jiffies record (kind 310) in this wg_advance")
  discard <| timerPassObserved jEnd
  let j ← liftPrefix (hiddenJiffies .jiffiesEnd)
  if j != jEnd then liftPrefix <| invariant "the end-of-wait jiffies record changed between the peek and the read"
  liftPrefix <| modify fun w => { w with jiffiesLast := some j }

theorem afterAdvanceObserved_erases : ErasesPrefix afterAdvanceObserved afterAdvance := by
  unfold afterAdvanceObserved afterAdvance
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | with_reducible exact timerPassObserved_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply map_erases
    | with_reducible apply erasesPrefix_bind
    | (with_reducible intro x; try dsimp only)
    | (split <;> try simp_all)

def advanceSyscallObserved (ticks : Nat) : PrefixM TimerObservation Int := do
  let ret ← liftPrefix (advancePrelude ticks)
  afterAdvanceObserved
  return ret

theorem advanceSyscallObserved_erases (ticks : Nat) :
    ErasesPrefix (advanceSyscallObserved ticks) (syscall (.wgAdvance ticks)) := by
  rw [syscallAdvance_factor]
  unfold advanceSyscallObserved
  exact erasesPrefix_bind (erasesPrefix_lift _) fun ret =>
    erasesPrefix_bind afterAdvanceObserved_erases fun _ => erasesPrefix_pure ret

end Leanux.Proofs.Logged
