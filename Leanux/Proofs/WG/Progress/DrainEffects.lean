import Leanux.Proofs.WG.Progress.DrainAuditSource
import Leanux.Proofs.WG.Progress.FlushQueueClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Campaign2 TimerDiscipline

theorem flushedSend_decreases (pid : PeerId) (d : Device) (entry final : WGWorld) (ambient after : Ambient)
    (resident : entry.dev = some d) (member : pid ∈ d.sendWorkQueue)
    (run : ((runFlushedSendWork pid).run entry).run ambient = .ok (((), final), after)) :
    ∃ next, final.dev = some next ∧
      flushQueueCount (workQueues next) + 1 = flushQueueCount (workQueues d) := by
  have queues := runFlushedSendWork_queues pid d entry ambient () final after resident run
  cases present : final.dev with
  | none => simp [flushQueueAt, flushQueueKernel, present] at queues
  | some next =>
    refine ⟨next, rfl, ?_⟩
    have same : workQueues next = flushedSendQueues pid d := by
      simpa [flushQueueAt, flushQueueKernel, present] using queues
    rw [same]
    exact flushedSendQueues_count pid d member

theorem flushedClear_decreases (pid : PeerId) (d : Device) (entry final : WGWorld) (ambient after : Ambient)
    (resident : entry.dev = some d) (member : pid ∈ d.clearWorkQueue)
    (run : ((runFlushedClearWork pid).run entry).run ambient = .ok (((), final), after)) :
    ∃ next, final.dev = some next ∧
      flushQueueCount (workQueues next) + 1 = flushQueueCount (workQueues d) := by
  have queues := runFlushedClearWork_queues pid d entry ambient () final after resident run
  cases present : final.dev with
  | none => simp [flushQueueAt, flushQueueKernel, present] at queues
  | some next =>
    refine ⟨next, rfl, ?_⟩
    have same : workQueues next = flushedClearQueues pid d := by
      simpa [flushQueueAt, flushQueueKernel, present] using queues
    rw [same]
    exact flushedClearQueues_count pid d member

theorem drainIncrement_bounded (upTo : Option PeerId) (count next : Nat)
    (result : DrainRaw) (decreases : next + 1 = count)
    (bounded : DrainBounded upTo next (projectDrain result)) :
    DrainBounded upTo count (projectDrain (drainIncrement result)) := by
  cases result with
  | error failure =>
    simp only [DrainBounded, projectDrain, drainIncrement, drainAttempts] at *
    exact ⟨by omega, bounded.2⟩
  | ok found =>
    rcases found with ⟨success, final, ambient⟩
    simp only [DrainBounded, projectDrain, drainIncrement, drainAttempts] at *
    exact ⟨by omega, bounded.2⟩

/-- Normal workers strictly decrease the selected queue measure. A failing
selector or worker stops immediately; neither is mislabeled as own exhaustion. -/
theorem drainAuditRun_bounded (upTo : Option PeerId) (fuel : Nat)
    (entry : WGWorld) (ambient : Ambient) (d : Device) (resident : entry.dev = some d)
    (enough : flushQueueCount (workQueues d) < fuel) :
    DrainBounded upTo (flushQueueCount (workQueues d))
      (projectDrain (drainAuditRun upTo fuel entry ambient)) := by
  induction fuel generalizing entry ambient d with
  | zero => omega
  | succ fuel ih =>
    unfold drainAuditRun
    cases selected : (drainSelect.run entry).run ambient with
    | error error => simp [projectDrain, DrainBounded, drainAttempts]
    | ok found =>
      rcases found with ⟨⟨choice, middle⟩, inputs⟩
      have facts := drainSelect_selected d entry ambient choice middle inputs resident selected
      cases choice with
      | drained =>
        rcases facts with ⟨same, sendEmpty, clearEmpty⟩
        simp [projectDrain, DrainBounded, drainAttempts, flushQueues, snapshot,
          core, same, workQueues, sendEmpty, clearEmpty]
      | send pid =>
        cases worker : ((runFlushedSendWork pid).run middle).run inputs with
        | error error => simp [worker, projectDrain, DrainBounded, drainAttempts]
        | ok found =>
          rcases found with ⟨⟨returned, final⟩, ending⟩
          cases returned
          simp only [worker]
          obtain ⟨next, present, decreases⟩ :=
            flushedSend_decreases pid d middle final inputs ending facts.1 facts.2 worker
          exact drainIncrement_bounded upTo _ _ _ decreases
            (ih final ending next present (by omega))
      | clear pid =>
        cases worker : ((runFlushedClearWork pid).run middle).run inputs with
        | error error => simp [worker, projectDrain, DrainBounded, drainAttempts]
        | ok found =>
          rcases found with ⟨⟨returned, final⟩, ending⟩
          cases returned
          simp only [worker]
          by_cases stop : upTo = some pid
          · simp [stop, projectDrain, DrainBounded, drainAttempts]
          · simp only [beq_iff_eq, stop, ↓reduceIte]
            obtain ⟨next, present, decreases⟩ :=
              flushedClear_decreases pid d middle final inputs ending facts.1 facts.2 worker
            exact drainIncrement_bounded upTo _ _ _ decreases
              (ih final ending next present (by omega))

end Leanux.Proofs.WG.Progress
