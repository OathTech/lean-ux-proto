import Leanux.Proofs.WG.Progress.AdvanceWaitModel
import Leanux.Proofs.WG.Progress.TimerWaitSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Original mode selection and bound reads. The recordless branch runs its
original work and has no recorded-wait receipt. -/
def afterAdvancePrefixWith (timers : UInt64 → Leanux.M Bool)
    (placeholder : UInt64 → Leanux.M Unit) : Leanux.M (Option AdvanceWaitReceipt) := do
  let w ← getWG
  let a ← getAmbient
  if a.hidden.isNone then
    let jHi := w.jiffiesLast.getD 0 + a.timing.advanceWait.toUInt64
    if a.hiddenPlaceholders then placeholder jHi else discard <| timers jHi
    return none
  let some jEnd ← peekSiteU64 .jiffiesEnd
    | throw (.hidden "no end-of-wait jiffies record (kind 310) in this wg_advance")
  let some (j0,j1) := (← getEnv).lastAdvance
    | invariant "afterAdvance without an advance"
  return some {j0,j1,jEnd}

def afterAdvancePrefix : Leanux.M (Option AdvanceWaitReceipt) :=
  afterAdvancePrefixWith runTimers runTimersPlaceholder

/-- Original timer pass and checked end read, at the captured distinct bounds. -/
def afterAdvanceSuffixWith (timers : UInt64 → Leanux.M Bool) : Option AdvanceWaitReceipt → Leanux.M Unit
  | none => pure ()
  | some receipt => do
    discard <| timers receipt.pass
    timerWaitFinish receipt.pass receipt.jEnd

def afterAdvanceSuffix : Option AdvanceWaitReceipt → Leanux.M Unit
  | none => afterAdvanceSuffixWith runTimers none
  | some receipt => afterAdvanceSuffixWith runTimers (some receipt)

/-- Decorate the actual call. A receipt is returned only after its original
timer pass, due-timer guard and consuming end read all return normally. -/
def observedAfterAdvance : Leanux.M (Option AdvanceWaitReceipt) := do
  let receipt ← afterAdvancePrefix
  afterAdvanceSuffix receipt
  pure receipt

/-- Complete original source factor, retaining both modes and every error. -/
theorem afterAdvance_source :
    afterAdvance = (afterAdvancePrefix >>= afterAdvanceSuffix) := by
  unfold afterAdvance afterAdvancePrefix afterAdvancePrefixWith
  simp only [bind_assoc]
  congr 1
  funext w
  congr 1
  funext a
  split
  · split <;> simp [afterAdvanceSuffix, afterAdvanceSuffixWith]
  · simp only [bind_assoc]
    congr 1
    funext seen
    cases seen with
    | none => rfl
    | some jEnd =>
      simp only [bind_assoc]
      congr 1
      funext env
      cases pair : env.lastAdvance with
      | none => rfl
      | some bounds =>
        obtain ⟨j0,j1⟩ := bounds
        simp [afterAdvanceSuffix,afterAdvanceSuffixWith,AdvanceWaitReceipt.pass,timerWaitFinish]

/-- Dropping the returned receipt runs exactly the original operation,
including its original stopped outcomes. -/
theorem observedAfterAdvance_erase :
    (do let _ ← observedAfterAdvance; pure ()) = afterAdvance := by
  rw [afterAdvance_source]
  simp only [observedAfterAdvance,bind_assoc,pure_bind]
  congr 1
  funext receipt
  cases receipt <;> simp [afterAdvanceSuffix]

/-- The decorated source fixes the receipt to the very prefix whose returned
value chooses the original continuation; this is not an independent witness. -/
theorem observedAfterAdvance_source :
    observedAfterAdvance = (do
      let receipt ← afterAdvancePrefix
      afterAdvanceSuffix receipt
      pure receipt) := rfl

/-- Normal recorded prefix runs expose the actual fixture pair and actual peek
from this entry, before any callback. They do not reconstruct an execution
state from the campaign projection. -/
theorem afterAdvancePrefix_recorded_provenance (initial final : World)
    (result : Option AdvanceWaitReceipt)
    (recorded : initial.ambient.hidden.isSome = true)
    (run : afterAdvancePrefix.run initial = .ok (result,final)) :
    ∃ receipt, result = some receipt ∧
      initial.fixture.lastAdvance = some (receipt.j0,receipt.j1) ∧
      (peekSiteU64 .jiffiesEnd : Leanux.M (Option UInt64)).run initial =
        .ok (some receipt.jEnd,initial) ∧ final = initial := by
  have present : initial.ambient.hidden.isNone = false := by
    cases hidden : initial.ambient.hidden <;> simp_all
  unfold afterAdvancePrefix afterAdvancePrefixWith at run
  change ((do
    if initial.ambient.hidden.isNone then
      let jHi := initial.wg.jiffiesLast.getD 0 + initial.ambient.timing.advanceWait.toUInt64
      if initial.ambient.hiddenPlaceholders then runTimersPlaceholder jHi else discard <| runTimers jHi
      return none
    let some jEnd ← peekSiteU64 .jiffiesEnd
      | throw (.hidden "no end-of-wait jiffies record (kind 310) in this wg_advance")
    let some (j0,j1) := (← getEnv).lastAdvance
      | invariant "afterAdvance without an advance"
    return some ({j0,j1,jEnd} : AdvanceWaitReceipt) : Leanux.M (Option AdvanceWaitReceipt)).run initial) = _ at run
  rw [present] at run
  simp only [Bool.false_eq_true,ite_false] at run
  let seen : Option UInt64 := match initial.ambient.hidden with
    | some rs => (rs.find? (·.site == HiddenSite.jiffiesEnd.info.id)).map fun r =>
        ((r.bytes.take HiddenSite.jiffiesEnd.info.len).foldr
          (fun (b : UInt8) (acc : Nat) => acc * 256 + b.toNat) 0).toUInt64
    | none => none
  have peek : (peekSiteU64 .jiffiesEnd : Leanux.M (Option UInt64)).run initial =
      .ok (seen,initial) := rfl
  rw [StateT.run_bind,peek] at run
  cases endpoint : seen with
  | none => simp only [endpoint] at run; cases run
  | some jEnd =>
    simp only [endpoint] at run
    dsimp only [Bind.bind,Except.bind] at run
    dsimp only [getEnv,StateT.run,Bind.bind,StateT.bind,get,getThe,
      MonadStateOf.get,StateT.get,Pure.pure,StateT.pure,Except.bind,Except.pure] at run
    cases advance : initial.fixture.lastAdvance with
    | none =>
      rw [advance] at run
      cases run
    | some pair =>
      obtain ⟨j0,j1⟩ := pair
      rw [advance] at run
      change Except.ok (some ({j0,j1,jEnd} : AdvanceWaitReceipt),initial) =
        Except.ok (result,final) at run
      cases run
      exact ⟨{j0,j1,jEnd},rfl,rfl,by simpa only [endpoint] using peek,rfl⟩
end Leanux.Proofs.WG.Progress
