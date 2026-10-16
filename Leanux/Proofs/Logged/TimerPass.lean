import Leanux.Proofs.Logged.Capture
import Leanux.Proofs.Logged.PrefixLoops
import Leanux.Env

/-! Completed original timer-pass units, observed on the proof side. A
crypt observation is a complete scheduler call, which may do no work. -/
namespace Leanux.Proofs.Logged
open Leanux Leanux.WG Leanux.Env

structure TimerObservation where
  worker : Option Worker
  execution : RunWitness Unit

def timerUnitObserved (worker : Option Worker) (a : Leanux.M Unit) : PrefixM TimerObservation Unit := do
  let execution ← captureRun a
  emitPrefix ⟨worker, execution⟩

theorem timerUnitObserved_run (worker : Option Worker) (a : Leanux.M Unit)
    (w : World) (h : List TimerObservation) :
    runPrefix (timerUnitObserved worker a) w h =
      match a.run w with
      | .error e => (.error e, h)
      | .ok ((), v) => (.ok ((), v), h ++ [⟨worker, ⟨(), w, v⟩⟩]) := by
  unfold timerUnitObserved
  rw [runPrefix_bind]
  cases hr : a.run w with
  | error e => simp [runPrefix_captureRun, hr]
  | ok out =>
    rcases out with ⟨⟨⟩, v⟩
    simp [runPrefix_captureRun, hr]

theorem timerUnitObserved_erases (worker : Option Worker) (a : Leanux.M Unit) :
    ErasesPrefix (timerUnitObserved worker a) a := by
  intro w h
  unfold timerUnitObserved
  rw [runPrefix_bind]
  cases hr : a.run w with
  | error e => simp [runPrefix_captureRun, hr]
  | ok out =>
    rcases out with ⟨⟨⟩, v⟩
    simp [runPrefix_captureRun, hr]

private theorem map_erases (f : α → β) {g : PrefixM Event α} {a : Leanux.M α}
    (h : ErasesPrefix g a) : ErasesPrefix (f <$> g) (f <$> a) := by
  simpa only [bind_pure_comp] using erasesPrefix_bind h (fun x => erasesPrefix_pure (f x))

/-- The complete committed timer unit, including passive records consumed by
unit lookup. Dispatch checks that can stop emit no successful receipt. -/
def timerDispatchUnit (w : Worker) (pid : PeerId) (t : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) : Leanux.M Unit := do
  let expected ← timerWorker t
  if w != expected then
    throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next ({expected.symbol}, bucket expiry {we.bucketExpiry}); the records show a section of {w.symbol}")
  -- dispatch order (docs/2026-10-11-dispatch-order.md): the timer the
  -- section names, by the address its arm record carried
  if let some u ← peekUnit w then
    match (← getWG).timerUnits.find? (·.1 == u) with
    | some (_, pid', t') =>
      if pid' != pid || t' != t then
        throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next; the section names peer {pid'}'s {repr t'}")
    | none => throw (.hidden s!"a section of {w.symbol} for a timer the mirror never armed ({u})")
  if let some b := step then
    if b != we.bucketExpiry then requireStepComplete b
  delTimer pid t
  modifyWG fun s => { s with timerPassStep := some we.bucketExpiry }
  runTimerSection w (WG.timerCallback pid t)
  modifyWG fun s => { s with timerPassStep := none }

def timerPassObserved (jHi : UInt64) : PrefixM TimerObservation Bool := do
  liftPrefix <| modifyWG fun w => { w with queuedThisCall := [] }
  if (← liftPrefix getWG).dev.isNone then return false
  let startOf (w : Worker) := (HiddenSite.sectionStart w).info.id
  let mut fired := false
  let mut step : Option UInt64 := none
  for _ in [0:(← liftPrefix recordBudget)] do
    let some site ← liftPrefix peekNextSite | break
    let d ← liftPrefix getDev
    if let some w := timerSectionOf site then
      if w == .clearPeerWorker then
        if let some b := step then
          liftPrefix (requireStepComplete b)
          step := none
        if d.clearWorkQueue.isEmpty then break
        timerUnitObserved (some w) runOneClearWorker
      else
        let some (pid, t, we) := TimerWheel.nextDue d jHi
          | liftPrefix <| throw (.hidden s!"a section of {w.symbol}, but no modeled timer's bucket is due by jiffies {jHi}")
        timerUnitObserved (some w) (timerDispatchUnit w pid t we step)
        step := some we.bucketExpiry
        fired := true
    else
      if let some b := step then
        liftPrefix (requireStepComplete b)
        step := none
      if !fired then break
      else if site == startOf .sendWorker && !d.sendWorkQueue.isEmpty then
        timerUnitObserved (some .sendWorker) runOneSendWorker
      else
        timerUnitObserved none runCryptWorkers
        if (← liftPrefix peekNextSite) == some site then break
  if let some b := step then liftPrefix (requireStepComplete b)
  if fired then
    liftPrefix deliverSent
    let d ← liftPrefix getDev
    if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
      liftPrefix <| unsupported "work a timer queued outlived the guest's wait"
  return fired

private theorem timerDispatchUnit_suffix_erases {α : Type} (w : Worker) (pid : PeerId) (t : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) (x : α) :
    ErasesPrefix (do timerUnitObserved (some w) (timerDispatchUnit w pid t we step); pure x)
      (do
        let expected ← timerWorker t
        if w != expected then
          throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next ({expected.symbol}, bucket expiry {we.bucketExpiry}); the records show a section of {w.symbol}")
        -- dispatch order (docs/2026-10-11-dispatch-order.md): the timer the
        -- section names, by the address its arm record carried
        if let some u ← peekUnit w then
          match (← getWG).timerUnits.find? (·.1 == u) with
          | some (_, pid', t') =>
            if pid' != pid || t' != t then
              throw (.hidden s!"the wheel runs peer {pid}'s {repr t} timer next; the section names peer {pid'}'s {repr t'}")
          | none => throw (.hidden s!"a section of {w.symbol} for a timer the mirror never armed ({u})")
        if let some b := step then
          if b != we.bucketExpiry then requireStepComplete b
        delTimer pid t
        modifyWG fun s => { s with timerPassStep := some we.bucketExpiry }
        runTimerSection w (WG.timerCallback pid t)
        modifyWG fun s => { s with timerPassStep := none }
        pure x) := by
  have stopped {α β : Type} (e : Stop) (f : α → Leanux.M β) :
      ((throw e : Leanux.M α) >>= f) = throw e := rfl
  have h := erasesPrefix_bind (timerUnitObserved_erases (some w)
    (timerDispatchUnit w pid t we step)) (fun _ => erasesPrefix_pure x)
  refine Eq.mp ?_ h
  congr 1
  unfold timerDispatchUnit
  simp only [bind_assoc, pure_bind, stopped]
  apply bind_congr
  intro expected
  by_cases he : (w != expected) = true
  · simp only [he, ite_true, stopped]
  · simp only [he, Bool.false_eq_true, ite_false, bind_assoc]
    apply bind_congr
    intro unit
    cases unit with
    | none =>
      cases step <;> simp only [bind_assoc]
      all_goals first
        | (solve | simp only [bind_assoc])
        | (split <;> simp only [bind_assoc])
    | some u =>
      simp only [bind_assoc]
      apply bind_congr
      intro state
      cases hn : state.timerUnits.find? (·.1 == u) with
      | none => simp only [hn, stopped]
      | some named =>
        rcases named with ⟨unused, pid', t'⟩
        simp only [hn]
        by_cases hd : (pid' != pid || t' != t) = true
        · simp only [hd, ite_true, stopped]
        · simp only [hd, Bool.false_eq_true, ite_false, bind_assoc]
          cases step <;> simp only [bind_assoc]
          all_goals first
            | (solve | simp only [bind_assoc])
            | (split <;> simp only [bind_assoc])

theorem timerPassObserved_erases (jHi : UInt64) :
    ErasesPrefix (timerPassObserved jHi) (runTimers jHi) := by
  unfold timerPassObserved runTimers
  repeat' first
    | (with_reducible
        change ErasesPrefix
          (do timerUnitObserved (some _) (timerDispatchUnit _ _ _ _ _); pure _) _
       exact timerDispatchUnit_suffix_erases _ _ _ _ _ _)
    | with_reducible exact timerUnitObserved_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply map_erases
    | with_reducible apply erasesPrefix_ite
    | with_reducible apply erasesPrefix_bind
    | (with_reducible intro x; try dsimp only)
    | (split <;> try simp_all only)

end Leanux.Proofs.Logged
