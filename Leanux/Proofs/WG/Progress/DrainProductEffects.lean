import Leanux.Proofs.WG.Progress.DrainEffects
import Leanux.Proofs.WG.Progress.DrainProductAuditSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Progress.Product
open Leanux Leanux.WG TimerDiscipline

theorem flushedSend_decreases (pid : PeerId) (d : Device) (entry final : World)
    (resident : entry.wg.dev = some d) (member : pid ∈ d.sendWorkQueue)
    (run : (liftWG (runFlushedSendWork pid)).run entry = .ok ((), final)) :
    ∃ next, final.wg.dev = some next ∧
      flushQueueCount (workQueues next) + 1 = flushQueueCount (workQueues d) := by
  change (((runFlushedSendWork pid).run entry.wg).run entry.ambient >>= fun ((value, current), inputs) =>
    .ok (value, {entry with wg := current, ambient := inputs})) = .ok ((), final) at run
  cases native : ((runFlushedSendWork pid).run entry.wg).run entry.ambient with
  | error err => rw [native] at run; cases run
  | ok pair =>
    obtain ⟨⟨value, current⟩, inputs⟩ := pair
    rw [native] at run
    cases run
    exact Progress.flushedSend_decreases pid d entry.wg current entry.ambient inputs resident member native

theorem flushedClear_decreases (pid : PeerId) (d : Device) (entry final : World)
    (resident : entry.wg.dev = some d) (member : pid ∈ d.clearWorkQueue)
    (run : (liftWG (runFlushedClearWork pid)).run entry = .ok ((), final)) :
    ∃ next, final.wg.dev = some next ∧
      flushQueueCount (workQueues next) + 1 = flushQueueCount (workQueues d) := by
  change (((runFlushedClearWork pid).run entry.wg).run entry.ambient >>= fun ((value, current), inputs) =>
    .ok (value, {entry with wg := current, ambient := inputs})) = .ok ((), final) at run
  cases native : ((runFlushedClearWork pid).run entry.wg).run entry.ambient with
  | error err => rw [native] at run; cases run
  | ok pair =>
    obtain ⟨⟨value, current⟩, inputs⟩ := pair
    rw [native] at run
    cases run
    exact Progress.flushedClear_decreases pid d entry.wg current entry.ambient inputs resident member native

theorem drainIncrement_bounded (upTo : Option PeerId) (count next : Nat)
    (result : DrainRaw) (decreases : next + 1 = count)
    (bounded : DrainBounded upTo next (projectDrain result)) :
    DrainBounded upTo count (projectDrain (drainIncrement result)) := by
  cases result with
  | error failure =>
    simp only [DrainBounded, projectDrain, drainIncrement, drainAttempts] at *
    exact ⟨by omega, bounded.2⟩
  | ok found =>
    rcases found with ⟨success, final⟩
    simp only [DrainBounded, projectDrain, drainIncrement, drainAttempts] at *
    exact ⟨by omega, bounded.2⟩

theorem drainAuditRun_bounded (upTo : Option PeerId) (fuel : Nat)
    (entry : World) (d : Device) (resident : entry.wg.dev = some d)
    (enough : flushQueueCount (workQueues d) < fuel) :
    DrainBounded upTo (flushQueueCount (workQueues d))
      (projectDrain (drainAuditRun upTo fuel entry)) := by
  have native := Progress.drainAuditRun_bounded upTo fuel entry.wg entry.ambient d resident enough
  unfold drainAuditRun
  cases audit : Progress.drainAuditRun upTo fuel entry.wg entry.ambient with
  | error failure =>
    simpa [audit, Except.map, projectDrain, Progress.projectDrain, DrainBounded,
      Progress.DrainBounded, drainAttempts, Progress.drainAttempts] using native
  | ok pair =>
    obtain ⟨success, final, ambient⟩ := pair
    cases reason : success.reason <;>
      simpa [audit, Except.map, projectDrain, Progress.projectDrain, DrainBounded,
        Progress.DrainBounded, drainAttempts, Progress.drainAttempts, Campaign2.Product.snapshot, reason] using native

end Leanux.Proofs.WG.Progress.Product
