import Leanux.Proofs.WG.TimerDiscipline.Model
import Leanux.Proofs.WG.TimerDiscipline.SelectionFrames
import Leanux.Proofs.WG.TimerDiscipline.FireRetrySource

/-! Current selected wheel-unit contracts. The outer nextDue branch and complete runTimers loop are separate obligations. -/

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env Noise Std.Do

theorem singleton_filter_member (ids : List PeerId) (test : PeerId → Bool) (pid : PeerId)
    (singleton : ids.filter test = [pid]) : pid ∈ ids ∧ test pid = true := by
  apply List.mem_filter.mp
  rw [singleton]
  simp

/-- Corrected to worker-kind and device preservation on the actual selected-unit prefix. The obsolete logical-expiry implication is refuted separately. -/
theorem timerSelection_due (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) (d : Device) :
    Noise.Product.Ensures (timerDispatchPrefix_variant worker pid timer we step)
      (fun w => w.wg.dev = some d)
      (fun _ w => worker.timer? = some timer ∧ w.wg.dev = some d) := by
  intro initial result final pre run
  have same := (Noise.Product.ensures_iff _ _ _).mpr
    (timerSelection_kernel_spec (fun g _ _ _ => g.dev = some d) worker pid timer we step)
    initial result final pre run
  refine ⟨?_, same⟩
  let expected : Worker := match timer with
    | .retransmitHandshake => .timerRetransmit
    | .sendKeepalive => .timerSendKeepalive
    | .newHandshake => .timerNewHandshake
    | .zeroKeyMaterial => .timerZeroKey
    | .persistentKeepalive => .timerPersistentKeepalive
  have workerRun : timerWorker timer = pure expected := by cases timer <;> rfl
  have chosen : worker = expected := by
    by_cases sameWorker : worker = expected
    · exact sameWorker
    · have wrong : (worker != expected) = true := by
        cases worker <;> cases timer <;> first | rfl | exact False.elim (sameWorker rfl)
      simp only [timerDispatchPrefix_variant, workerRun, pure_bind, wrong, ite_true] at run
      cases run
  rw [chosen]
  cases timer <;> rfl

/-- Corrected selected-unit retry effect conditional on its actual prefix run; this does not establish outer wheel selection. -/
theorem fireTimer_retransmit (pid : PeerId) (we : WheelEntry) (step : Option UInt64)
    (identity attempts : Nat) (timer : Option UInt64) :
    Noise.Product.Ensures (timerDispatchUnit_variant .timerRetransmit pid .retransmitHandshake we step)
      (fun w => retryAt w.wg pid = some (identity, attempts, timer) ∧
        ∃ selected, (timerDispatchPrefix_variant .timerRetransmit pid .retransmitHandshake we step).run w =
          .ok ((), selected))
      (fun _ w => retryAt w.wg pid = some (identity, nextAttempts attempts, none)) := by
  intro initial result final pre run
  obtain ⟨counter, selected, selection⟩ := pre
  have frame := (Noise.Product.ensures_iff _ _ _).mpr
    (timerSelection_kernel_spec (fun g _ _ _ => retryAt g pid = some (identity, attempts, timer))
      .timerRetransmit pid .retransmitHandshake we step)
  have after := frame initial () selected counter selection
  rw [fireTimer_source, StateT.run_bind, selection] at run
  exact fireSelected_retransmit pid we identity attempts timer selected result final after run

theorem duePeer_resident (d : Device) (timer : PeerTimer) (jHi : UInt64) (pid : PeerId)
    (member : pid ∈ duePeers d timer jHi) :
    pid ∈ d.peerList ∧ ∃ p expiry, d.peers[pid]? = some p ∧
      p.timer timer = some expiry ∧ timeBefore expiry jHi = true := by
  obtain ⟨listed, due⟩ := List.mem_filter.mp member
  refine ⟨listed, ?_⟩
  change (match d.peers[pid]?.bind (fun p => p.timer timer) with
    | some expiry => timeBefore expiry jHi
    | none => false) = true at due
  cases resident : d.peers[pid]? with
  | none => simp [resident] at due
  | some p =>
    cases armed : p.timer timer with
    | none => simp [resident, armed] at due
    | some expiry =>
      exact ⟨p, expiry, rfl, armed, by simpa [resident, armed] using due⟩

/-- Exact prefix and detached suffix of an already selected wheel unit. No peer-list or logical-expiry inference is made. -/
theorem fireTimer_execution (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) (step : Option UInt64) (initial final : World) (d : Device)
    (device : initial.wg.dev = some d)
    (run : (timerDispatchUnit_variant worker pid timer we step).run initial = .ok ((), final)) :
    ∃ selected,
      (timerDispatchPrefix_variant worker pid timer we step).run initial = .ok ((), selected) ∧
      (fireWheelSelected worker pid timer we).run selected = .ok ((), final) ∧
      worker.timer? = some timer ∧ selected.wg.dev = some d := by
  rw [fireTimer_source, StateT.run_bind] at run
  cases selection : (timerDispatchPrefix_variant worker pid timer we step).run initial with
  | error stop => rw [selection] at run; cases run
  | ok pair =>
    obtain ⟨value, selected⟩ := pair
    cases value
    rw [selection] at run
    exact ⟨selected, rfl, run,
      timerSelection_due worker pid timer we step d initial () selected device selection⟩

end Leanux.Proofs.WG.TimerDiscipline
