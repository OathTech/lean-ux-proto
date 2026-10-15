import Leanux.Proofs.WG.TimerDiscipline.Model
import Leanux.Proofs.WG.TimerDiscipline.SelectionFrames
import Leanux.Proofs.WG.TimerDiscipline.FireRetrySource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem singleton_filter_member (ids : List PeerId) (test : PeerId → Bool) (pid : PeerId)
    (singleton : ids.filter test = [pid]) : pid ∈ ids ∧ test pid = true := by
  apply List.mem_filter.mp
  rw [singleton]
  simp

theorem timerSelection_due (worker : Worker) (jHi : UInt64) (d : Device) :
    Ensures (timerSelection worker jHi) (fun w => w.k.wg = some d)
      (fun selected w => worker.timer? = some selected.2 ∧
        selected.1 ∈ duePeers d selected.2 jHi ∧ w.k.wg = some d) := by
  have hp := peekUnit_spec_kernel_variant (fun k => k.wg = some d) worker
  rw [ensures_iff]
  mvcgen [timerSelection, getDev, getK, invariant, unsupported, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [duePeers]
  all_goals grind [singleton_filter_member]

theorem fireTimer_retransmit (pid : PeerId) (jHi : UInt64)
    (identity attempts : Nat) (timer : Option UInt64) :
    Ensures (fireTimer .timerRetransmit jHi)
      (fun w => retryAt w pid = some (identity, attempts, timer) ∧
        ∃ selected, (timerSelection .timerRetransmit jHi).run w =
          .ok ((pid, .retransmitHandshake), selected))
      (fun _ w => retryAt w pid = some (identity, nextAttempts attempts, none)) := by
  intro initial result final pre run
  obtain ⟨counter, selected, selection⟩ := pre
  have frame := (ensures_iff _ _ _).mpr
    (timerSelection_kernel_spec (fun k => retryKernel k pid = some (identity, attempts, timer))
      .timerRetransmit jHi)
  have after : retryAt selected pid = some (identity, attempts, timer) :=
    frame initial _ selected counter selection
  rw [fireTimer_source, StateT.run_bind, selection] at run
  exact fireSelected_retransmit pid identity attempts timer selected result final after run

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

theorem fireTimer_execution (worker : Worker) (jHi : UInt64) (initial final : World) (d : Device)
    (device : initial.k.wg = some d) (run : (fireTimer worker jHi).run initial = .ok ((), final)) :
    ∃ pid timer selected,
      (timerSelection worker jHi).run initial = .ok ((pid, timer), selected) ∧
      (fireSelected worker pid timer).run selected = .ok ((), final) ∧
      worker.timer? = some timer ∧ selected.k.wg = some d ∧
      pid ∈ d.peerList ∧ ∃ p expiry, d.peers[pid]? = some p ∧
        p.timer timer = some expiry ∧ timeBefore expiry jHi = true := by
  rw [fireTimer_source, StateT.run_bind] at run
  cases selection : (timerSelection worker jHi).run initial with
  | error e => rw [selection] at run; cases run
  | ok pair =>
    obtain ⟨⟨pid, timer⟩, selected⟩ := pair
    rw [selection] at run
    have contract := timerSelection_due worker jHi d initial (pid, timer) selected device selection
    exact ⟨pid, timer, selected, rfl, run, contract.1, contract.2.2,
      duePeer_resident d timer jHi pid contract.2.1⟩

end Leanux.Proofs.WG.TimerDiscipline
