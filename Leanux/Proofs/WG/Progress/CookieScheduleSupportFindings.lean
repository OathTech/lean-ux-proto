import Leanux.Proofs.WG.Progress.CookieRingFindings
import Leanux.Proofs.WG.Progress.CookieSchedulerSource
import Leanux.Proofs.WG.Progress.CookieScheduleControlModel
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Recomputing the remaining count after a productive consume need not compose
with consuming the initial count. This is a malformed-tail witness, not reachability. -/
theorem cookieBadTail_count_composition_false (msg : List UInt8) (src : SkbSource) :
    let ring := cookieBadTailRing msg src
    ring.items ≠ [] ∧
      cookieRingAfter ring.consume.2.count ring.consume.2 ≠ cookieRingAfter ring.count ring := by
  simp [cookieBadTailRing, cookieRingAfter, PtrRing.count, PtrRing.items, PtrRing.consume,
    PtrRing.peek, PtrRing.discardOne, PtrRing.discardOne.clear]

namespace CookieFull

/-- A physical hole is permitted by the old logical CookieOnly/nonempty domain.
The actual probe encounters a hidden-site mismatch and declines to resume. This
refutes even the return-tag part of the old projected total contract. The concrete
state is solely an existential counterexample, with no reachability assertion. -/
theorem turn_cookieHole_counterexample :
    ∃ (a : Activation) (d : Device) (bytes stop : List UInt8),
      a.worker = .receiveWorker ∧ d.indexTable = [] ∧ CookieOnly d ∧
      bytes.length = 8 ∧ stop.length = 8 ∧ d.handshakeQueue.items ≠ [] ∧
      ¬ Campaign2.Product.Returns (scheduleTurn none)
        (fun entry => entry.wg.device = some d ∧
          entry.ambient.hidden = some (records [bytes] stop) ∧ entry.ambient.suspended = [a])
        (fun value _ => value = turnContinue) := by
  let base : World := {
    ambient := {env := fun _ _ => false, timing := {advanceWait := 0, traceBound := 0}}
    tasks := {task := {files := {count := 1, resizeInProgress := false, nextFd := 0, fdt := {maxFds := 0, fd := #[], openFds := #[], closeOnExec := #[]}}, rlimitNofile := 0}}
    fs := {} }
  let src : SkbSource := {family := 0, saddr := 0, sport := 0, daddr := 0, iif := 0}
  let msg : List UInt8 := [3, 0, 0, 0]
  let d : Device := {
    ifindex := 0
    ifname := "wg0"
    handshakeQueue := {size := 3, batch := 16, producer := 2, consumerHead := 0, consumerTail := 0, slots := #[none, some (msg, src), none]}
    handshakeQueueLen := 1 }
  let a : Activation := {worker := .receiveWorker}
  let bytes : List UInt8 := List.replicate 8 0
  let stop : List UInt8 := List.replicate 8 0
  let w := {base with
    wg := {base.wg with dev := some d}
    ambient := {base.ambient with hidden := some (records [bytes] stop), suspended := [a]}}
  have items : d.handshakeQueue.items = [(msg, src)] := by
    simp [d, PtrRing.items, PtrRing.count, List.range_succ]
  have cookies : CookieOnly d := by
    intro packet source member
    rw [items] at member
    simp only [List.mem_singleton, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    rfl
  have count : d.handshakeQueue.count = 2 := by simp [d, PtrRing.count]
  have actual : (scheduleTurn none).run w = .ok (turnReturn, w) := by
    have mismatch : ∃ reason, resolveCookieRead false (records [bytes] stop) = .error (.hidden reason) := by
      unfold resolveCookieRead
      rw [records_drop]
      exact ⟨_, rfl⟩
    obtain ⟨reason, mismatch⟩ := mismatch
    have activation : (Activation.run a).run w = .error (.hidden reason) := by
      rw [cookieEmptyActivation_run a rfl w d (records [bytes] stop) rfl rfl rfl, mismatch]
    have bounded : cookieHybridRun a d.handshakeQueue.count w = .error (.hidden reason) := by
      rw [← cookieActivation_run a w d (records [bytes] stop) rfl rfl rfl cookies rfl]
      exact activation
    have peek : (peekHiddenSite : Leanux.M (Option Nat)).run w =
        .ok (some HiddenSite.reschedReceive.info.id, w) := by
      have read := cookiePeek_run w (records [bytes] stop) rfl
      rw [records_drop] at read
      simpa [records, control, cookieControlSite, w] using read
    have resolved : resolveCookieActivation d.handshakeQueue.count (records [bytes] stop) =
        .ok ⟨1, true, records [] stop⟩ := by
      rw [count]
      exact resolve_yield 1 bytes [] stop (by simp [bytes])
    rw [cookieScheduler_run a w d _ _ rfl rfl rfl cookies rfl rfl resolved]
    simp only [cookieBoundedScheduler, StateT.run_bind, peek]
    dsimp only [bind, Except.bind, StateT.run]
    rw [bounded]
    rfl
  refine ⟨a, d, bytes, stop, rfl, rfl, cookies,
    by simp [bytes], by simp [stop], by simp [items], ?_⟩
  intro total
  obtain ⟨value, final, run, result⟩ := total w ⟨rfl, rfl, rfl⟩
  rw [actual] at run
  cases run
  cases result

end CookieFull
end Leanux.Proofs.WG.Progress
