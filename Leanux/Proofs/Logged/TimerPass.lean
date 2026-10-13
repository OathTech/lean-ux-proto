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

def timerUnitObserved (worker : Option Worker) (a : M Unit) : PrefixM TimerObservation Unit := do
  let execution ← captureRun a
  emitPrefix ⟨worker, execution⟩

theorem timerUnitObserved_run (worker : Option Worker) (a : M Unit)
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

theorem timerUnitObserved_erases (worker : Option Worker) (a : M Unit) :
    ErasesPrefix (timerUnitObserved worker a) a := by
  intro w h
  unfold timerUnitObserved
  rw [runPrefix_bind]
  cases hr : a.run w with
  | error e => simp [runPrefix_captureRun, hr]
  | ok out =>
    rcases out with ⟨⟨⟩, v⟩
    simp [runPrefix_captureRun, hr]

private theorem map_erases (f : α → β) {g : PrefixM Event α} {a : M α}
    (h : ErasesPrefix g a) : ErasesPrefix (f <$> g) (f <$> a) := by
  simpa only [bind_pure_comp] using erasesPrefix_bind h (fun x => erasesPrefix_pure (f x))

def timerPassObserved (jHi : UInt64) : PrefixM TimerObservation Bool := do
  liftPrefix <| modify fun w => { w with queuedThisCall := [] }
  if (← liftPrefix getK).wg.isNone then return false
  let startOf (w : Worker) := (HiddenSite.sectionStart w).info.id
  let mut fired := false
  for _ in [0:(← liftPrefix recordBudget)] do
    let some site ← liftPrefix peekNextSite | break
    let d ← liftPrefix getDev
    if let some w := timerSectionOf site then
      if w == .clearPeerWorker then
        if d.clearWorkQueue.isEmpty then break
        timerUnitObserved (some w) runOneClearWorker
      else
        timerUnitObserved (some w) (fireTimer w jHi)
        fired := true
    else if !fired then break
    else if site == startOf .sendWorker && !d.sendWorkQueue.isEmpty then
      timerUnitObserved (some .sendWorker) runOneSendWorker
    else
      timerUnitObserved none runCryptWorkers
      if (← liftPrefix peekNextSite) == some site then break
  if fired then
    liftPrefix deliverSent
    let d ← liftPrefix getDev
    if !d.sendWorkQueue.isEmpty || !d.clearWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty then
      liftPrefix <| unsupported "work a timer queued outlived the guest's wait"
  return fired

theorem timerPassObserved_erases (jHi : UInt64) :
    ErasesPrefix (timerPassObserved jHi) (runTimers jHi) := by
  unfold timerPassObserved runTimers
  repeat' first
    | with_reducible exact timerUnitObserved_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply map_erases
    | with_reducible apply erasesPrefix_bind
    | (with_reducible intro x; try dsimp only)
    | (split <;> try simp_all)

end Leanux.Proofs.Logged
