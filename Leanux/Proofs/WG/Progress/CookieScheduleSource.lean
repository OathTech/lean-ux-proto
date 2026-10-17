import Leanux.Proofs.WG.Progress.CookieScheduleOutcomeSource
import Leanux.Proofs.WG.Progress.CookieScheduleFrames
import Leanux.Proofs.WG.Progress.CookieSchedulerSource

/-! Actual original scheduler turns and full-loop adequacy. Each yielded activation is probed, detached, and committed by the original scheduler; the supplied record budget includes the final return turn. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CookieFull
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Progress

theorem turn_stop (a : Activation) (w : World) (d : Device) (stop : List UInt8)
    (receive : a.worker = .receiveWorker) (device : w.k.wg = some d)
    (table : d.indexTable = []) (cookies : CookieOnly d)
    (present : w.hidden = some (records [] stop)) (suspended : w.suspended = [a])
    (len : stop.length = 8) :
    (scheduleTurn none).run w = .ok (turnContinue, finished w d) := by
  rw [cookieScheduler_run a w d _ _ receive device table cookies present suspended
    (resolve_stop d.handshakeQueue.length stop len)]
  simp [cookieActivationWorld, records_drop, detached, suspended, activation_ne_self,
    cookieFinalSteps, finished]
theorem turn_yield (a : Activation) (w : World) (d : Device) (bytes : List UInt8)
    (ys : List (List UInt8)) (stop : List UInt8)
    (receive : a.worker = .receiveWorker) (device : w.k.wg = some d)
    (table : d.indexTable = []) (cookies : CookieOnly d)
    (present : w.hidden = some (records (bytes::ys) stop)) (suspended : w.suspended = [a])
    (len : bytes.length = 8) (nonempty : d.handshakeQueue ≠ []) :
    (scheduleTurn none).run w = .ok (turnContinue, yieldedWorld a w d (records ys stop)) := by
  cases queue : d.handshakeQueue with
  | nil => exact False.elim (nonempty queue)
  | cons head tail =>
    have resolved := resolve_yield tail.length bytes ys stop len
    rw [← List.length_cons (a := head), ← queue] at resolved
    rw [cookieScheduler_run a w d _ _ receive device table cookies present suspended resolved]
    simp [cookieActivationWorld, records_drop, detached, suspended, activation_ne_self,
      cookieFinalSteps, cookieProcessedSteps, yieldedWorld, cookieTailDevice]
theorem turn_finished (w : World) (d : Device) (device : w.k.wg = some d)
    (hiddenEmpty : w.hidden = some []) (suspendedEmpty : w.suspended = []) :
    (scheduleTurn none).run w = .ok (turnReturn,w) := by
  have peek : peekHiddenSite.run w = .ok (none,w) := by
    simpa only [List.dropWhile_nil, List.head?_nil, Option.map_none, ← hiddenEmpty] using cookiePeek_run w [] hiddenEmpty
  have filter : (w.suspended.filterM Activation.consistent).run w = .ok ([],w) := by
    rw [suspendedEmpty]; rfl
  exact turn_no_candidates none w w none d (by simp [hiddenEmpty]) peek (by simp) device
    (by simp) filter

def schedulerLoop (turns : List Nat) : M (Option Unit × Unit) :=
  forIn turns (none,()) (fun _ _ => scheduleTurn none)
theorem schedulerLoop_run (ys : List (List UInt8)) (turns : List Nat)
    (a : Activation) (w : World) (d : Device) (stop : List UInt8)
    (receive : a.worker = .receiveWorker) (device : w.k.wg = some d)
    (table : d.indexTable = []) (cookies : CookieOnly d)
    (present : w.hidden = some (records ys stop)) (suspended : w.suspended = [a])
    (valid : ∀ bytes ∈ ys, bytes.length = 8) (stopLen : stop.length = 8)
    (occupancy : ys.length ≤ d.handshakeQueue.length) (fuel : ys.length+2 ≤ turns.length) :
    (schedulerLoop turns).run w = .ok ((some (),()), finished w d) := by
  induction ys generalizing turns a w d with
  | nil =>
    cases turns with
    | nil => simp at fuel
    | cons turn turns =>
      cases turns with
      | nil => simp at fuel
      | cons next turns =>
        have first := turn_stop a w d stop receive device table cookies present suspended stopLen
        have last := turn_finished (finished w d)
          {d with handshakeQueue := [], handshakeQueueLen := d.handshakeQueueLen-d.handshakeQueue.length}
          rfl rfl rfl
        simp only [schedulerLoop, List.forIn_cons, StateT.run_bind]
        rw [first]
        change ((do let step ← scheduleTurn none
                    match step with
                    | .done value => pure value
                    | .yield value => forIn turns value (fun _ _ => scheduleTurn none)).run (finished w d)) = _
        rw [StateT.run_bind, last]
        rfl
  | cons bytes ys ih =>
    cases turns with
    | nil => simp at fuel
    | cons turn turns =>
      have nonempty : d.handshakeQueue ≠ [] := by
        intro empty
        simp [empty] at occupancy
      have byteLen : bytes.length = 8 := valid bytes (by simp)
      have first := turn_yield a w d bytes ys stop receive device table cookies present suspended byteLen nonempty
      have nextCookies : CookieOnly (cookieTailDevice d) := by
        intro m src member
        apply cookies m src
        exact List.mem_of_mem_drop member
      have nextOccupancy : ys.length ≤ (cookieTailDevice d).handshakeQueue.length := by
        simp only [cookieTailDevice, List.length_drop, List.length_cons] at occupancy ⊢
        omega
      have nextFuel : ys.length+2 ≤ turns.length := by
        simp only [List.length_cons] at fuel
        omega
      have next := ih turns {a with iterations := a.iterations+1}
        (yieldedWorld a w d (records ys stop)) (cookieTailDevice d)
        receive rfl table nextCookies rfl rfl (by intro b hb; exact valid b (by simp [hb]))
        nextOccupancy nextFuel
      simp only [schedulerLoop, List.forIn_cons, StateT.run_bind]
      rw [first]
      change (schedulerLoop turns).run (yieldedWorld a w d (records ys stop)) = _
      rw [next, final_composition a w d (records ys stop) nonempty]


end Leanux.Proofs.WG.Progress.CookieFull
