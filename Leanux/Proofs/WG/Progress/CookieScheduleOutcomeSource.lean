import Leanux.Proofs.WG.Progress.CookieScheduleControlModel
import Leanux.Proofs.WG.Progress.CookieSchedulerSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress.CookieFull
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Progress

/-- The first actual bounded cookie resumption, followed by the unchanged
scheduler remainder and its original budget guard. No tail classification or
drain is inferred from the initial logical ring view. -/
def boundedSchedule (a : Activation) (occupancy remaining : Nat) : Leanux.M Unit := do
  let first ← cookieBoundedScheduler a occupancy
  let result ← match first with
    | .done value => pure value
    | .yield value => forIn (List.range' 1 remaining) value (fun _ _ => scheduleTurn none)
  match result.1 with
  | some ret => pure ret
  | none => budgetExhausted "the scheduler loop"

/-- Corrected exact outcome factor on the entire historical schedule domain.
Control-record validity determines the first resumption branch; the actual
bounded receive and original remaining turns retain every error and return. -/
theorem schedule_run (ys : List (List UInt8)) (a : Activation) (w : World)
    (d : Device) (stop : List UInt8)
    (receive : a.worker = .receiveWorker) (device : w.wg.dev = some d)
    (table : d.indexTable = []) (cookies : CookieOnly d)
    (present : w.ambient.hidden = some (records ys stop)) (suspended : w.ambient.suspended = [a])
    (valid : ∀ bytes ∈ ys, bytes.length = 8) (stopLen : stop.length = 8)
    (occupancy : ys.length ≤ d.handshakeQueue.count) :
    (schedule none).run w = (boundedSchedule a d.handshakeQueue.count (ys.length + 1)).run w := by
  have first : (scheduleTurn none).run w = (cookieBoundedScheduler a d.handshakeQueue.count).run w := by
    cases ys with
    | nil =>
      exact cookieScheduler_run a w d _ _ receive device table cookies present suspended
        (resolve_stop d.handshakeQueue.count stop stopLen)
    | cons bytes ys =>
      have positive : 0 < d.handshakeQueue.count := by simp only [List.length_cons] at occupancy; omega
      have counted : d.handshakeQueue.count - 1 + 1 = d.handshakeQueue.count := by omega
      have resolved := resolve_yield (d.handshakeQueue.count - 1) bytes ys stop (valid bytes (by simp))
      rw [counted] at resolved
      exact cookieScheduler_run a w d _ _ receive device table cookies present suspended resolved
  have budget : (recordBudget : Leanux.M Nat).run w = .ok (ys.length + 2, w) := by
    change Except.ok ((match w.ambient.hidden with
      | some rs => rs.length + 1
      | none => DOMAIN_FILTER_TURNS), w) = _
    simp [present, records, Nat.add_assoc]
  rw [schedule_source, StateT.run_bind, budget]
  change ((do let result ← forIn [0:ys.length + 2] ((none, ()) : Option Unit × Unit)
                (fun _ _ => scheduleTurn none)
              match result.1 with
              | some ret => pure ret
              | none => budgetExhausted "the scheduler loop").run w) = _
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [show ys.length + 2 = (ys.length + 1) + 1 from rfl, List.range'_succ]
  simp only [List.forIn_cons, bind_assoc, StateT.run_bind, first, boundedSchedule]
  cases actual : (cookieBoundedScheduler a d.handshakeQueue.count).run w with
  | error stop => rfl
  | ok pair =>
    obtain ⟨step, middle⟩ := pair
    cases step <;> rfl

end Leanux.Proofs.WG.Progress.CookieFull
