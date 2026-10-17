import Leanux.Syscalls
import Leanux.Proofs.WG.Progress.AdvanceWaitSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Every actual successful ioctl advances the stored bounds by the requested
unsigned delta. This includes the recordless branch and imposes no readiness. -/
theorem advance_normal_bounds (ticks : Nat) (initial final : World) (result : Int)
    (run : (advance ticks).run initial = .ok (result,final)) :
    result = 0 ∧ ∃ j0 j1, final.fixture.lastAdvance = some (j0,j1) ∧
      j1 - j0 = ticks.toUInt64 ∧ final.wg.jiffiesLast = some j1 := by
  let read : AmbientM (UInt64 × UInt64) := do
    if initial.ambient.hidden.isNone && initial.ambient.hiddenPlaceholders then
      let j0 := initial.wg.jiffiesLast.getD 0
      pure (j0,j0 + ticks.toUInt64)
    else
      if !initial.ambient.armRecords then
        unsupported "a time advance without arm records (the timers' expiries are unknown)"
      let bs ← hidden .timeAdvance
      pure (WG.recordWord64 bs 0,WG.recordWord64 bs 1)
  have factor : (advance ticks).run initial = ((read.run initial.ambient) >>= fun (bounds,inputs) =>
    ((do
      if bounds.2 - bounds.1 != ticks.toUInt64 then
        throw (.hidden s!"the advance moved jiffies from {bounds.1} to {bounds.2}, not by {ticks}")
      modifyWG fun w => {w with jiffiesLast := some bounds.2}
      modifyEnv fun e => {e with lastAdvance := some bounds}
      pure (0 : Int) : Leanux.M Int).run {initial with ambient := inputs})) := by
    dsimp only [advance,getWG,getAmbient,StateT.run,Bind.bind,StateT.bind,
      Pure.pure,StateT.pure,Except.pure,Except.bind,get,getThe,MonadStateOf.get,StateT.get,
      monadLift,MonadLift.monadLift,liftM,liftWG,liftAmbient]
    cases mode : (initial.ambient.hidden.isNone && initial.ambient.hiddenPlaceholders) <;>
      cases armed : initial.ambient.armRecords
    all_goals simp only [read,mode,armed,Bool.not_true,Bool.not_false,Bool.false_eq_true,
      ite_false,ite_true]
    all_goals first | rfl |
      (cases record : (AmbientM.hidden .timeAdvance).run initial.ambient <;>
        dsimp only [StateT.run] at record <;>
        simp [hidden,monadLift,MonadLift.monadLift,liftAmbient,StateT.run,
          Bind.bind,StateT.bind,Pure.pure,StateT.pure,Except.pure,Except.bind,record])
  rw [factor] at run
  cases readRun : read.run initial.ambient with
  | error stop => rw [readRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨j0,j1⟩,inputs⟩ := pair
    rw [readRun] at run
    dsimp only [Bind.bind,Except.bind] at run
    by_cases delta : j1 - j0 = ticks.toUInt64
    · simp only [delta,bne_self_eq_false,Bool.false_eq_true,ite_false] at run
      cases run
      exact ⟨rfl,j0,j1,rfl,delta,rfl⟩
    · have different : (j1 - j0 != ticks.toUInt64) = true := by simp [delta]
      rw [different] at run
      cases run

/-- The original syscall entry resets and seccomp guard before KCOV dispatch.
The guard retains its original unsupported outcome. -/
def advanceOperationEntry : Leanux.M Unit := do
  modify fun w => {w with
    fs := {w.fs with userOut := none,userFds := none}
    seccomp := {w.seccomp with emitted := {},translatedLen := none}}
  modifyWG fun g => {g with queuedThisCall := []}
  modifyAmbient fun a => {a with steps := #[],extraOut := [],fired := #[],netRxSections := 0,netRxSection := 0}
  if (← getCurrent).seccomp.mode != .disabled then
    unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)"

/-- The actual dispatch and return work, after the unchanged entry guards. -/
def advanceOperationPrefix (ticks : Nat) : Leanux.M Int := do
  advanceOperationEntry
  let ret ← dispatch (.wgAdvance ticks)
  for c in Env.windowTailCalls do liftSeccomp (Seccomp.enterHarnessCall c)
  taskWorkRun
  return ret

/-- Exact original syscall factor, including all modes and errors. -/
theorem syscall_advance_source (ticks : Nat) :
    syscall (.wgAdvance ticks) = (do
      let ret ← advanceOperationPrefix ticks
      afterAdvance
      pure ret) := by
  unfold syscall advanceOperationPrefix advanceOperationEntry
  simp only [syscallNr,Syscall.isNet,Bool.true_and,bind_assoc]
  congr 1
  funext reset
  congr 1
  funext queued
  congr 1
  funext cleared
  congr 1
  funext task
  split <;> simp only [pure_bind]

/-- The pair read here is the actual fixture value after this syscall's ioctl
and return work. The wait receipt is optional because both source modes run. -/
def observedAdvanceOperation (ticks : Nat) : Leanux.M
    (Int × Option (UInt64 × UInt64) × Option AdvanceWaitReceipt) := do
  let ret ← advanceOperationPrefix ticks
  let bounds := (← getEnv).lastAdvance
  let receipt ← observedAfterAdvance
  return (ret,bounds,receipt)

/-- Receipt erasure preserves the exact original syscall, including every Stop. -/
theorem observedAdvanceOperation_erase (ticks : Nat) :
    (do let result ← observedAdvanceOperation ticks; pure result.1) = syscall (.wgAdvance ticks) := by
  rw [syscall_advance_source]
  unfold observedAdvanceOperation
  simp only [bind_assoc,pure_bind]
  congr 1
  funext ret
  rw [← observedAfterAdvance_erase]
  simp only [bind_assoc,pure_bind]
  rfl

end Leanux.Proofs.WG.Progress
