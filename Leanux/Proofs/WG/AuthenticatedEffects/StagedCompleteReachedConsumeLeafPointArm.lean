import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumeLeafPointJoin

/-! The real arm body exposes its WG metadata writes, guards, snapshot reads
and actual receipt. Wheel installation remains a distinct native child because
its cached peer write can precede a failing validation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

noncomputable def failedWGShape (body : WG.M α) (next : α → WG.M β) (failure : Failure (wg body)) :
    Shape (wg (body >>= next)) := by
  rw [wg_bind]
  exact .failed failure (fun value => wg (next value))

elab "consume_leaf_bound_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  let body ← if action.isAppOf ``wg then
      match action.getAppArgs.back? with
      | some body => pure body
      | none => Lean.throwError "missing body"
    else do
      unless action.isAppOf ``liftWGObserver do Lean.throwError "not observer"
      let some observer := action.getAppArgs.back? | Lean.throwError "missing observer"
      unless observer.isAppOf ``liftWGPrefix do Lean.throwError "not native"
      let some body := observer.getAppArgs.back? | Lean.throwError "missing native"
      pure body
  let body := body.consumeMData.headBeta
  unless body.isAppOf ``Bind.bind do Lean.throwError "not bind"
  let args := body.getAppArgs
  let some head := args[args.size - 2]? | Lean.throwError "missing first action"
  let .const actual _ := head.consumeMData.headBeta.getAppFn | Lean.throwError "not constant"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different first action"

def armClock (pid : PeerId) (t : PeerTimer) (w : WGWorld) (jm e : UInt64) (u : Nat) : WG.M Unit := do
  let cb ← hidden .timerClk
  let (clk, u2) := (recordWord64 cb 0, recordWord cb 1)
  if u != 0 && u2 != u then
    throw (.hidden s!"the base-clock record names timer {u2}, the arm record {u}")
  if timeAfter clk (jm + 1) then
    throw (.hidden s!"the timer base's clock {clk} is more than one past mod_timer's read {jm}")
  if let some prev := (← get).timerClk then
    if timeBefore clk prev then
      throw (.hidden s!"the timer base's clock went back: {clk} after {prev}")
  if let some b := TimerWheel.earliestDue (← getDev) jm then
    if timeAfter clk b then
      throw (.hidden s!"the timer base's clock {clk} is past the overdue modeled bucket {b} (forward_timer_base stops at next_expiry)")
  if let some step := w.timerPassStep then
    if !timeAfter clk step then
      throw (.hidden s!"an arm inside a timer pass at step {step} with the base clock {clk} not past it")
  modify fun k => { k with timerClk := some clk }
  placeOnWheel pid t e clk (some u)

def armInstall (pid : PeerId) (t : PeerTimer) (w : WGWorld) (jm e : UInt64) (bs : List UInt8) : WG.M Unit := do
  modify fun w => { w with jiffiesLast := some jm }
  let u := recordWord bs 2
  if u != 0 then modify fun w => { w with timerUnits := (u, pid, t) :: w.timerUnits.filter (·.1 != u) }
  if (← getPeer pid).timer t == some e then return
  armClock pid t w jm e u

def armRecorded (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc? : Option UInt64) (w : WGWorld) : WG.M Unit := do
  let bs ← hidden .modTimerArm
  let (jm, e) := (recordWord64 bs 0, recordWord64 bs 1)
  let some jc := jc? | invariant "a timer armed with arm records and no caller read (kind 311)"
  let expires := jc + delay.toUInt64       -- `expires = jiffies + delay`, the caller's arithmetic
  if expires != e then
    throw (.hidden s!"timer expiry differs from Linux: the caller read jiffies {jc} and mod_timer published {e}; the mirror's delay {delay} gives {expires}")
  let gap := (jm - jc).toInt64             -- `(long)(J_m - J_c)`
  if gap < 0 then
    throw (.hidden s!"mod_timer's jiffies {jm} is behind the caller's read {jc} (delay {delay}, expires {e})")
  if gap > 1 then
    unsupported s!"a stall between a timer's two jiffies reads (the mirror's delay matches the published expiry): the caller's {jc}, mod_timer's {jm} (delay {delay}, expires {e})"
  armInstall pid t w jm e bs

theorem arm_native_factor (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc? : Option UInt64) :
    armTimer pid t delay jc? = (do
      let w ← get
      if !(← getAmbient).armRecords then
        let j0 := w.jiffiesLast.getD 0
        placeOnWheel pid t (j0 + delay.toUInt64) j0 none
        return
      armRecorded pid t delay jc? w) := rfl

macro "consume_leaf_arm_step" : tactic => `(tactic| first
    | (consume_leaf_bound_head «throw»; exact failedWGShape _ _ (.wgThrow _))
    | (consume_leaf_bound_head invariant; exact failedWGShape _ _ (.wgInvariant _))
    | (consume_leaf_bound_head unsupported; exact failedWGShape _ _ (.wgUnsupported _))
    | (consume_leaf_wg_head placeOnWheel; exact .child (.wheel _ _ _ _ _))
    | (consume_leaf_wg_head modify; refine .native (.change _ ?_); intro w; rfl)
    | (consume_leaf_wg_head «throw»; exact .native (.failure _))
    | consume_leaf_shape)

noncomputable def armClockShape (pid : PeerId) (t : PeerTimer) (w : WGWorld) (jm e : UInt64) (u : Nat) :
    Shape (wg (armClock pid t w jm e u)) := by
  unfold armClock
  repeat' consume_leaf_arm_step

noncomputable def armInstallShape (pid : PeerId) (t : PeerTimer) (w : WGWorld) (jm e : UInt64) (bs : List UInt8) :
    Shape (wg (armInstall pid t w jm e bs)) := by
  unfold armInstall
  repeat' first
    | (consume_leaf_wg_head armClock; exact armClockShape _ _ _ _ _ _)
    | consume_leaf_arm_step

noncomputable def armRecordedShape (pid : PeerId) (t : PeerTimer) (delay : Nat) (jc? : Option UInt64) (w : WGWorld) :
    Shape (wg (armRecorded pid t delay jc? w)) := by
  unfold armRecorded
  repeat' first
    | (consume_leaf_wg_head armInstall; exact armInstallShape _ _ _ _ _ _)
    | consume_leaf_arm_step

noncomputable def armNativeShape (pid : PeerId) (timer : PeerTimer) (delay : Nat) (clock : Option UInt64) :
    Shape (wg (armTimer pid timer delay clock)) := by
  rw [arm_native_factor]
  repeat' first
    | (consume_leaf_wg_head armRecorded; exact armRecordedShape _ _ _ _ _)
    | consume_leaf_arm_step

theorem arm_factor (pid : PeerId) (timer : PeerTimer) (delay : Nat) (clock : Option UInt64) :
    liftWGObserver (effects.arm pid timer delay clock) = (do
      let h ← historyRead
      liftWGObserver (TimerEffects.armReceipt Event.armed (CausalScope.current scope? h) pid timer delay clock)) := by
  funext w h
  rfl

noncomputable def armShape (pid : PeerId) (timer : PeerTimer) (delay : Nat) (clock : Option UInt64) :
    Shape (liftWGObserver (effects.arm pid timer delay clock)) := by
  rw [arm_factor]
  refine .bind (.native .history) ?_
  intro h
  unfold TimerEffects.armReceipt
  rw [Points.wg_receipt_factor]
  exact .bind (.native (.base (.basic .world))) (fun before =>
    .bind (armNativeShape pid timer delay clock) (fun value =>
      .bind (.native (.base (.basic .world))) (fun after =>
        .bind (.native (.armed ⟨CausalScope.current scope? h,pid,timer,delay,clock,
          ⟨value,before.wg,after.wg,before.ambient,after.ambient⟩⟩)) (fun _ => .pure value))))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
