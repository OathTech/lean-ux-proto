import Leanux.Proofs.WG.Progress.CookieBoundedSource
import Leanux.Proofs.WG.Progress.ScheduleTurn

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

theorem cookieRead_next (yielded : Bool) (records : List HiddenRecord)
    (bytes : List UInt8) (rest : List HiddenRecord)
    (run : resolveCookieRead yielded records = .ok (bytes,rest)) :
    cookieNext records = some (cookieControlSite yielded).info.id := by
  unfold resolveCookieRead at run
  cases stripped : records.dropWhile (fun r => HiddenSite.passive r.site) with
  | nil => simp [stripped] at run
  | cons record tail =>
    simp only [stripped] at run
    split at run
    · cases run
    · rename_i same
      have site : record.site = (cookieControlSite yielded).info.id := by simpa using same
      simp [cookieNext, stripped, site]

theorem cookieActivation_drop (count : Nat) (records : List HiddenRecord) :
    resolveCookieActivation count (records.dropWhile fun r => HiddenSite.passive r.site) =
      resolveCookieActivation count records := by
  cases count with
  | zero => simp [resolveCookieActivation, resolveCookieRead, cookie_drop_idem]
  | succ count =>
    simp [resolveCookieActivation, cookieReschedResult, cookie_drop_idem, cookieNext_drop]

theorem cookieActivation_next (count : Nat) (records : List HiddenRecord)
    (summary : CookieActivationSummary)
    (run : resolveCookieActivation count records = .ok summary) :
    cookieNext records = some HiddenSite.reschedReceive.info.id ∨
      cookieNext records = some (HiddenSite.sectionStop .receiveWorker).info.id := by
  induction count generalizing records summary with
  | zero =>
    simp only [resolveCookieActivation] at run
    cases read : resolveCookieRead false records with
    | error error => simp [read] at run
    | ok pair => exact Or.inr (cookieRead_next false records pair.1 pair.2 read)
  | succ count ih =>
    by_cases next : cookieNext records = some HiddenSite.reschedReceive.info.id
    · exact Or.inl next
    · simp only [resolveCookieActivation, cookieReschedResult, ite_eq_right next] at run
      unfold cookieIncrement at run
      cases resolved : resolveCookieActivation count (records.dropWhile fun r => HiddenSite.passive r.site) with
      | error error => simp [resolved, Except.map] at run
      | ok out =>
        have result := ih _ out resolved
        simpa only [cookieNext_drop] using result

/-- Run the exact bounded activation after the actual singleton detachment. -/
def cookieBoundedResumption (a : Activation) (occupancy : Nat) : Leanux.M TurnResult := fun w =>
  cookieHybridRun a occupancy (detached w a) >>= fun out => .ok (turnContinue, out.2)

/-- The current scheduler probes a copy and commits a separately detached run.
Only a hidden mismatch excludes the candidate. Other errors propagate exactly. -/
def cookieBoundedScheduler (a : Activation) (occupancy : Nat) : Leanux.M TurnResult := do
  let _ ← peekHiddenSite
  let accepted ← (fun w => probeResult w (cookieHybridRun a occupancy w) : Leanux.M Bool)
  if accepted then cookieBoundedResumption a occupancy else pure turnReturn

/-- Correction: pure control-record success selects the resumption branch but
does not establish actual activation success. This factor retains both actual
bounded runs and their precise error, return, suspension and exhaustion outcomes. -/
theorem cookieScheduler_run (a : Activation) (w : World) (d : Device)
    (records : List HiddenRecord) (summary : CookieActivationSummary)
    (receive : a.worker = .receiveWorker) (device : w.wg.dev = some d)
    (table : d.indexTable = []) (cookies : CookieOnly d) (present : w.ambient.hidden = some records)
    (suspended : w.ambient.suspended = [a])
    (resolve : resolveCookieActivation d.handshakeQueue.count records = .ok summary) :
    (scheduleTurn none).run w = (cookieBoundedScheduler a d.handshakeQueue.count).run w := by
  let afterPeek := {w with ambient := {w.ambient with
    hidden := some (records.dropWhile fun r => HiddenSite.passive r.site)}}
  have probe := cookieActivation_run a afterPeek d _ receive device table cookies rfl
  have actual := cookieActivation_run a (detached afterPeek a) d _ receive device table cookies rfl
  have next := cookieActivation_next d.handshakeQueue.count records summary resolve
  have noStart : ∀ worker, (cookieNext records).bind sectionOf ≠ some (worker, true) := by
    intro worker
    rcases next with next | next <;> rw [next] <;> cases worker <;> decide
  have noPoll : ((cookieNext records) == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false := by
    rcases next with next | next <;> simp [next, HiddenSite.info, Worker.sectionId, Worker.index]
  rw [turn_resumption none w afterPeek (cookieNext records) d
    (by simp [present]) (cookiePeek_run w records present) noStart device noPoll]
  have same : afterPeek.ambient.suspended = [a] := suspended
  rw [same]
  simp only [cookieBoundedScheduler, StateT.run_bind, cookiePeek_run w records present]
  change (([a].filterM Activation.consistent).run afterPeek >>= fun out =>
    (resumeCandidates none out.1).run out.2) =
    (probeResult afterPeek (cookieHybridRun a d.handshakeQueue.count afterPeek) >>= fun out =>
      ((if out.1 then cookieBoundedResumption a d.handshakeQueue.count else pure turnReturn) : Leanux.M TurnResult).run out.2)
  simp only [List.filterM, List.filterAuxM, StateT.run_bind, consistent_exact, probe]
  cases tested : cookieHybridRun a d.handshakeQueue.count afterPeek with
  | error error => cases error <;> rfl
  | ok pair =>
    obtain ⟨u, final⟩ := pair
    change (resumeCandidates none [a]).run afterPeek = _
    rw [resumeCandidates_singleton, actual]
    rfl

end Leanux.Proofs.WG.Progress
