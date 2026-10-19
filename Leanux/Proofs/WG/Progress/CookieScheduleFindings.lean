import Leanux.Proofs.WG.Progress.CookieScheduleOutcomeSource
import Leanux.Proofs.WG.Progress.CookieActivationBoundFindings

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress.CookieFull
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Progress

/-- The historical malformed-tail schedule witness now completes under the
refill-aware activation budget, including the copied-world consistency probe and
the committed detached run. No initialized reachability claim is made. -/
theorem schedule_cookieBadTail_completes (base : World) :
    ∃ (a : Activation) (w : World) (d : Device) (stop : List UInt8),
      a.worker = .receiveWorker ∧ w.wg.dev = some d ∧ d.indexTable = [] ∧ CookieOnly d ∧
      stop.length = 8 ∧ w.ambient.hidden = some (records [] stop) ∧ w.ambient.suspended = [a] ∧
      ([] : List (List UInt8)).length ≤ d.handshakeQueue.count ∧
      (schedule none).run w = .ok ((), cookieBadTailFinal (detached w a) d) := by
  let src : SkbSource := {family := 0, saddr := 0, sport := 0, daddr := 0, iif := 0}
  let msg : List UInt8 := [3, 0, 0, 0]
  let d : Device := {
    ifindex := 0
    ifname := "wg0"
    handshakeQueue := cookieBadTailRing msg src
    handshakeQueueLen := 1 }
  let a : Activation := {worker := .receiveWorker}
  let stop : List UInt8 := List.replicate 8 0
  let w := {base with
    wg := {base.wg with dev := some d}
    ambient := {base.ambient with hidden := some (records [] stop), suspended := [a]}}
  have cookies : CookieOnly d := by
    intro bytes source member
    have items : d.handshakeQueue.items = [(msg, src)] := by
      simp [d, cookieBadTailRing, PtrRing.items, PtrRing.count, PtrRing.peek]
    rw [items] at member
    simp only [List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    rfl
  refine ⟨a, w, d, stop, rfl, rfl, rfl, cookies, by simp [stop], rfl, rfl, by simp, ?_⟩
  let final := cookieBadTailFinal (detached w a) d
  have activation := cookieBadTail_activation_run a w d msg src rfl rfl rfl rfl rfl rfl
  have committed := cookieBadTail_activation_run a (detached w a) d msg src
    rfl rfl rfl rfl rfl rfl
  have candidates : ([a].filterM Activation.consistent).run w = .ok ([a], w) := by
    simp only [List.filterM, List.filterAuxM, StateT.run_bind, consistent_exact, activation]
    rfl
  have peek : (peekHiddenSite : Leanux.M (Option Nat)).run w =
      .ok (some (HiddenSite.sectionStop .receiveWorker).info.id, w) := by
    have read := cookiePeek_run w (records [] stop) rfl
    rw [records_drop] at read
    exact read
  have first : (scheduleTurn none).run w = .ok (turnContinue, final) := by
    have run := turn_resumes_singleton w w
      (some (HiddenSite.sectionStop .receiveWorker).info.id) d a rfl peek
      (by intro worker; cases worker <;> decide) rfl rfl candidates
    rw [committed] at run
    exact run
  have finalSuspended : final.ambient.suspended = [] := by
    change [a].filter (· != a) = []
    simp only [List.filter_cons, activation_ne_self, Bool.false_eq_true, ite_false, List.filter_nil]
  have finalPeek : (peekHiddenSite : Leanux.M (Option Nat)).run final = .ok (none, final) := by
    exact cookiePeek_run final [] rfl
  have finalCandidates : (final.ambient.suspended.filterM Activation.consistent).run final =
      .ok ([], final) := by
    rw [finalSuspended]
    rfl
  have last : (scheduleTurn none).run final = .ok (turnReturn, final) :=
    turn_no_candidates none final final none (cookieRingTailDevice (cookieRingTailDevice d))
      rfl finalPeek (by intro worker; simp) rfl rfl finalCandidates
  have budget : (recordBudget : Leanux.M Nat).run w = .ok (2, w) := by rfl
  rw [schedule_source, StateT.run_bind, budget]
  change ((do
    let result ← forIn [0:2] ((none, ()) : Option Unit × Unit) (fun _ _ => scheduleTurn none)
    match result.1 with
    | some ret => pure ret
    | none => budgetExhausted "the scheduler loop").run w) = _
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  simp only [List.range'_succ, List.range'_zero, List.forIn_cons, StateT.run_bind]
  rw [first]
  dsimp only [turnContinue, StateT.run, StateT.bind, StateT.pure, Except.pure,
    Bind.bind, Pure.pure, Except.bind]
  change scheduleTurn none final = .ok (turnReturn, final) at last
  rw [last]
  rfl

end Leanux.Proofs.WG.Progress.CookieFull
