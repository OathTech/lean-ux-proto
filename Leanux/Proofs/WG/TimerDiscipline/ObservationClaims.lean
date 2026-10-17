import Leanux.Proofs.WG.TimerDiscipline.HookObservationClaims
import Leanux.Proofs.WG.TimerDiscipline.ObservationBridge
import Leanux.Proofs.WG.TimerDiscipline.JitterBoundClaims
import Leanux.Proofs.WG.TimerDiscipline.JitterOutcomeClaims

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

theorem projected_timer_dispatch_due (worker : Worker) (jHi : UInt64) (d : Device) :
    Campaign2.Ensures (observed (Env.fireTimer worker jHi) (timerExecutionPath worker jHi))
      (fun s => s.wg.device = some d)
      (fun result final => ∃ pid timer selected,
        result.1 = .ok ((pid, timer, selected), final) ∧
        worker.timer? = some timer ∧ selected.wg.device = some d ∧
        pid ∈ d.peerList ∧ ∃ p expiry, d.peers[pid]? = some p ∧
          p.timer timer = some expiry ∧ timeBefore expiry jHi = true) := by
  apply observed_effect
  intro initial result final device run
  cases result
  obtain ⟨pid, timer, selected, selection, callback, kind, same, due⟩ :=
    source_timer_dispatch_due worker jHi initial final d device run
  refine ⟨pid, timer, snapshot selected, ?_, kind, same, due⟩
  apply observe_ok
  simp only [timerExecutionPath, StateT.run_bind, selection]
  change ((fireSelected worker pid timer).run selected >>= fun out =>
    Except.ok ((pid, timer, snapshot selected), out.2)) = _
  rw [callback]; rfl

theorem projected_retransmit_dispatch (pid : PeerId) (jHi : UInt64)
    (identity attempts : Nat) (timer : Option UInt64) :
    Campaign2.Ensures (observed (Env.fireTimer .timerRetransmit jHi)
      (timerSelection .timerRetransmit jHi))
      (fun s => retryObservation s pid = some (identity, attempts, timer))
      (fun result final => ∀ selected,
        result.1 = .ok ((pid, .retransmitHandshake), selected) →
        retryObservation final pid = some (identity, nextAttempts attempts, none)) := by
  apply observed_effect
  intro initial result final pre run selected selection
  cases hp : (timerSelection .timerRetransmit jHi).run initial with
  | error e => simp [observeResult, hp, Except.map] at selection
  | ok pair =>
    obtain ⟨⟨actualPid, actualTimer⟩, middle⟩ := pair
    rw [observe_ok hp] at selection
    obtain ⟨values, _⟩ := Prod.mk.inj (Except.ok.inj selection)
    obtain ⟨pidEq, timerEq⟩ := Prod.mk.inj values
    subst actualPid
    subst actualTimer
    exact source_retransmit_dispatch pid jHi identity attempts timer initial result final
      ⟨pre, middle, hp⟩ run

end Leanux.Proofs.WG.TimerDiscipline
