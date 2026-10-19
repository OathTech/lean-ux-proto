import Leanux.Proofs.WG.TimerDiscipline.WheelDispatchSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env

/-- One actual record-driven turn, including the original break paths. -/
def timerOuterTurn (jPass : UInt64) (_ : Nat)
    (state : Bool × Option UInt64) : Leanux.M (ForInStep (Bool × Option UInt64)) := do
  let some site ← peekNextSite | return .done state
  let d ← getDev
  if let some w := timerSectionOf site then
    if w == .clearPeerWorker then
      if let some b := state.2 then requireStepComplete b
      if d.clearWorkQueue.isEmpty then return .done (state.1, none)
      runOneClearWorker
      return .yield (state.1, none)
    else
      let some (pid, t, we) := TimerWheel.nextDue d jPass
        | throw (.hidden s!"a section of {w.symbol}, but no modeled timer's bucket is due by jiffies {jPass}")
      timerDispatchUnit_variant w pid t we state.2
      return .yield (true, some we.bucketExpiry)
  else
    if let some b := state.2 then requireStepComplete b
    if !state.1 then return .done (state.1, none)
    else if site == (HiddenSite.sectionStart .sendWorker).info.id && !d.sendWorkQueue.isEmpty then
      runOneSendWorker
      return .yield (state.1, none)
    else
      runCryptWorkers
      if (← peekNextSite) == some site then return .done (state.1, none)
      return .yield (state.1, none)

/-- The unchanged post-loop step, delivery and queue checks. -/
def timerOuterFinish (state : Bool × Option UInt64) : Leanux.M Bool := do
  if let some b := state.2 then requireStepComplete b
  if state.1 then
    deliverSent
    let d ← getDev
    if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
      unsupported "work a timer queued outlived the guest's wait"
  return state.1

def runTimersLoopSource (jPass : UInt64) : Leanux.M Bool := do
  modifyWG fun w => { w with queuedThisCall := [] }
  if (← getWG).dev.isNone then return false
  let state ← forIn [0:(← recordBudget)] (false, none) (timerOuterTurn jPass)
  timerOuterFinish state

/-- Source factoring only: no callback-success or progress premise. -/
theorem runTimers_loop_source (jPass : UInt64) :
    runTimersLoopSource jPass = Env.runTimers jPass := by
  rw [← runTimers_wheel_source]
  unfold runTimersLoopSource runTimersWheelSource runTimersWheelWith
  apply bind_congr
  intro reset
  apply bind_congr
  intro g
  by_cases absent : g.dev.isNone = true
  · simp only [absent, ite_true]
  · simp only [absent]
    apply bind_congr
    intro budget
    congr 1
    · apply congrArg (fun (body : Nat → (Bool × Option UInt64) → Leanux.M (ForInStep (Bool × Option UInt64))) =>
        forIn ([:budget] : Std.Legacy.Range) (false, none) body)
      funext turn state
      rcases state with ⟨fired, step⟩
      cases fired <;> cases step <;> simp only [timerOuterTurn]
      all_goals repeat' first
        | rfl
        | split
        | (congr 1; funext x)

/-- Remaining original turns after a successful first selected timer unit.
The budget was captured before that unit consumes any records. -/
def firstTimerContinuation (jPass : UInt64) (remaining : Nat) (we : WheelEntry) : Leanux.M Bool := do
  let state ← forIn (List.range' 1 remaining) (true, some we.bucketExpiry) (timerOuterTurn jPass)
  timerOuterFinish state

/-- The actual first selected unit followed by the original suffix. Any error
in the unit, suffix, or final checks is returned unchanged. -/
def firstTimerSelectedSource (jPass : UInt64) (worker : Worker)
    (pid : PeerId) (timer : PeerTimer) (we : WheelEntry) : Leanux.M Bool := do
  modifyWG fun w => { w with queuedThisCall := [] }
  let budget ← recordBudget
  timerDispatchUnit_variant worker pid timer we none
  firstTimerContinuation jPass (budget - 1) we

/-- Exact first-turn equality at the actual product entry. The only domain
conditions describe the initial record and actual wheel selection. -/
theorem runTimers_first_timer_run (jPass : UInt64) (worker : Worker)
    (pid : PeerId) (timer : PeerTimer) (we : WheelEntry)
    (initial : World) (d : Device) (site : Nat)
    (device : initial.wg.dev = some d)
    (nextSite : (initial.ambient.hidden.bind fun rs =>
      (rs.find? fun r => !HiddenSite.passive r.site).map (·.site)) = some site)
    (sectionMatch : timerSectionOf site = some worker)
    (notClear : worker ≠ .clearPeerWorker)
    (selected : TimerWheel.nextDue d jPass = some (pid, timer, we)) :
    (Env.runTimers jPass).run initial =
      (firstTimerSelectedSource jPass worker pid timer we).run initial := by
  let start : World := { initial with wg := { initial.wg with queuedThisCall := [] } }
  let remaining : Nat := match initial.ambient.hidden with
    | some records => records.length
    | none => DOMAIN_FILTER_TURNS - 1
  have budget : (recordBudget : Leanux.M Nat).run start = .ok (remaining + 1, start) := by
    change Except.ok ((match initial.ambient.hidden with
      | some rs => rs.length + 1
      | none => DOMAIN_FILTER_TURNS), start) = _
    dsimp only [remaining]
    cases initial.ambient.hidden <;> rfl
  have peek : peekNextSite.run start = .ok (some site, start) := by
    unfold peekNextSite
    rw [StateT.run_bind]
    change ((Except.ok (initial.ambient, start) : Except Stop _) >>= _) = _
    dsimp only [Bind.bind, Except.bind]
    cases records : initial.ambient.hidden with
    | none => simp [records] at nextSite
    | some rs =>
      change Except.ok (((rs.find? fun r => !HiddenSite.passive r.site).map (·.site)), start) = _
      simpa only [records, Option.bind_some] using congrArg (fun value => Except.ok (value, start)) nextSite
  have readDevice : (getDev : Leanux.M Device).run start = .ok (d, start) := by
    change (((getDev).run start.wg).run start.ambient >>= fun ((value, g), a) =>
      Except.ok (value, {start with wg := g, ambient := a})) = _
    simp [getDev, show start.wg.dev = some d from device]
  have notClearBool : (worker == .clearPeerWorker) = false := by
    cases worker <;> first | rfl | exact False.elim (notClear rfl)
  have first : (timerOuterTurn jPass 0 (false, none)).run start =
      ((do timerDispatchUnit_variant worker pid timer we none
           pure (ForInStep.yield (true, some we.bucketExpiry))) : Leanux.M _).run start := by
    unfold timerOuterTurn
    rw [StateT.run_bind, peek]
    change ((getDev : Leanux.M Device).run start >>= _) = _
    rw [readDevice]
    dsimp only [Bind.bind, Except.bind]
    simp only [sectionMatch, notClearBool, Bool.false_eq_true, ite_false, selected]
    rfl
  rw [← runTimers_loop_source]
  change ((do if initial.wg.dev.isNone then return false
              let state ← forIn [0:(← recordBudget)] (false, none) (timerOuterTurn jPass)
              timerOuterFinish state).run start) =
    ((do let budget ← recordBudget
         timerDispatchUnit_variant worker pid timer we none
         firstTimerContinuation jPass (budget - 1) we).run start)
  simp only [device, Option.isNone_some, Bool.false_eq_true, ite_false]
  rw [StateT.run_bind, budget]
  change ((do let state ← forIn [0:remaining + 1] (false, none) (timerOuterTurn jPass)
              timerOuterFinish state).run start) = _
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, List.range'_succ, List.forIn_cons, bind_assoc]
  rw [StateT.run_bind, first]
  simp only [StateT.run_bind, budget]
  dsimp only [Bind.bind, Except.bind]
  cases unitRun : (timerDispatchUnit_variant worker pid timer we none).run start with
  | error stop => rfl
  | ok out =>
    obtain ⟨value, next⟩ := out
    cases value
    rfl

end Leanux.Proofs.WG.TimerDiscipline
