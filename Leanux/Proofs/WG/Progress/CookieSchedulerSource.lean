import Leanux.Proofs.WG.Progress.CookieActivationFrames
set_option autoImplicit false
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

theorem cookieScheduler_run (a : Activation) (w : World) (d : Device)
    (records : List HiddenRecord) (summary : CookieActivationSummary)
    (receive : a.worker = .receiveWorker) (device : w.k.wg = some d)
    (table : d.indexTable = []) (cookies : CookieOnly d) (present : w.hidden = some records)
    (suspended : w.suspended = [a])
    (resolve : resolveCookieActivation d.handshakeQueue.length records = .ok summary) :
    (scheduleTurn none).run w = .ok (turnContinue,
      cookieActivationWorld a (detached {w with hidden := some (records.dropWhile fun r => HiddenSite.passive r.site)} a) d summary) := by
  let afterPeek := {w with hidden := some (records.dropWhile fun r => HiddenSite.passive r.site)}
  have parsed : resolveCookieActivation d.handshakeQueue.length
      (records.dropWhile fun r => HiddenSite.passive r.site) = .ok summary := by
    rw [cookieActivation_drop, resolve]
  have probe := cookieActivation_run a afterPeek d _ receive device table cookies rfl
  rw [parsed] at probe
  have actual := cookieActivation_run a (detached afterPeek a) d _ receive device table cookies rfl
  rw [parsed] at actual
  have candidates : (afterPeek.suspended.filterM Activation.consistent).run afterPeek = .ok ([a], afterPeek) := by
    have same : afterPeek.suspended = [a] := suspended
    rw [same]
    have consistent : (Activation.consistent a).run afterPeek = .ok (true, afterPeek) := by
      rw [consistent_exact, probe]
      rfl
    simp only [List.filterM, List.filterAuxM, StateT.run_bind]
    rw [consistent]
    rfl
  have next := cookieActivation_next d.handshakeQueue.length records summary resolve
  have noStart : ∀ worker, (cookieNext records).bind sectionOf ≠ some (worker,true) := by
    intro worker
    rcases next with next | next <;> rw [next] <;> cases worker <;> decide
  have noPoll : ((cookieNext records) == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false := by
    rcases next with next | next <;> simp [next, HiddenSite.info, Worker.sectionId, Worker.index]
  rw [turn_resumes_singleton w afterPeek (cookieNext records) d a
    (by simp [present]) (cookiePeek_run w records present) noStart device noPoll candidates, actual]
  rfl

end Leanux.Proofs.WG.Progress
