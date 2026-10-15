import Leanux.Proofs.WG.Progress.DrainSelectionSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Campaign2

abbrev DrainRaw := Except DrainFailure (DrainSuccess × World)

def drainIncrement : DrainRaw → DrainRaw
  | .error failure => .error { failure with attempts := failure.attempts + 1 }
  | .ok (success, final) => .ok ({ success with attempts := success.attempts + 1 }, final)

/-- A phase audit of actual original selector and worker executions. Errors
have no final state, just as the original state/error monad has none. -/
def drainAuditRun (upTo : Option PeerId) : Nat → World → DrainRaw
  | 0, _ => .error ⟨.ownBudget, .invariant "handshake_send_wq did not drain", 0⟩
  | fuel + 1, entry =>
    match drainSelect.run entry with
    | .error error => .error ⟨.selection, error, 1⟩
    | .ok (.drained, selected) => .ok (⟨.empty, 1⟩, selected)
    | .ok (.send pid, selected) =>
      match (runFlushedSendWork pid).run selected with
      | .error error => .error ⟨.sendWorker pid, error, 1⟩
      | .ok (_, final) => drainIncrement (drainAuditRun upTo fuel final)
    | .ok (.clear pid, selected) =>
      match (runFlushedClearWork pid).run selected with
      | .error error => .error ⟨.clearWorker pid, error, 1⟩
      | .ok (_, final) =>
        if upTo == some pid then .ok (⟨.requestedClear pid, 1⟩, final)
        else drainIncrement (drainAuditRun upTo fuel final)

def drainEraseRaw : DrainRaw → Except Stop (Unit × World)
  | .error failure => .error failure.error
  | .ok (_, final) => .ok ((), final)

def projectDrain : DrainRaw → DrainOutcome
  | .error failure => .error failure
  | .ok (success, final) => .ok (success, snapshot final)

def observedDrain (upTo : Option PeerId) : M DrainOutcome := fun entry =>
  .ok (projectDrain (drainAuditRun upTo 4096 entry), entry)

theorem drainIncrement_erases (result : DrainRaw) :
    drainEraseRaw (drainIncrement result) = drainEraseRaw result := by
  cases result <;> rfl

private theorem except_error_bind {α β : Type} (e : Stop) (f : α → Except Stop β) :
    (Except.error e >>= f) = .error e := rfl

private theorem except_ok_bind {α β : Type} (x : α) (f : α → Except Stop β) :
    (Except.ok x >>= f) = f x := rfl

/-- Finite evaluator correspondence with the original range-loop body. -/
theorem drainAuditRun_range (upTo : Option PeerId) (fuel start : Nat) (entry : World) :
    drainEraseRaw (drainAuditRun upTo fuel entry) =
      (do let state ← forIn (List.range' start fuel) (none, ()) (drainTurn upTo)
          drainFinish state).run entry := by
  induction fuel generalizing start entry with
  | zero => rfl
  | succ fuel ih =>
    simp only [List.range'_succ, List.forIn_cons]
    unfold drainAuditRun
    simp only [drainTurn, bind_assoc]
    cases hs : drainSelect.run entry with
    | error error => simp [hs, StateT.run_bind, StateT.run_pure, StateT.run_map, except_error_bind, except_ok_bind, drainEraseRaw]
    | ok found =>
      rcases found with ⟨selected, middle⟩
      cases selected with
      | drained =>
        simp [hs, StateT.run_bind, StateT.run_pure, StateT.run_map, except_error_bind, except_ok_bind,
          drainSelectedTurn, drainFinish, drainEraseRaw]
        rfl
      | send pid =>
        cases hw : (runFlushedSendWork pid).run middle with
        | error error => simp [hs, hw, StateT.run_bind, StateT.run_pure, StateT.run_map, except_error_bind, except_ok_bind,
            drainSelectedTurn, drainEraseRaw]
        | ok found =>
          rcases found with ⟨_, final⟩
          simpa [hs, hw, StateT.run_bind, StateT.run_pure, StateT.run_map, except_error_bind, except_ok_bind,
            drainSelectedTurn, drainIncrement_erases] using ih (start + 1) final
      | clear pid =>
        cases hw : (runFlushedClearWork pid).run middle with
        | error error => simp [hs, hw, StateT.run_bind, StateT.run_pure, StateT.run_map, except_error_bind, except_ok_bind,
            drainSelectedTurn, drainEraseRaw]
        | ok found =>
          rcases found with ⟨_, final⟩
          by_cases stop : upTo = some pid
          · simp [hs, hw, stop, StateT.run_bind, StateT.run_pure, StateT.run_map, except_error_bind, except_ok_bind,
              drainSelectedTurn, drainFinish, drainEraseRaw]
          · simpa [hs, hw, stop, StateT.run_bind, StateT.run_pure, StateT.run_map, except_error_bind, except_ok_bind,
              drainSelectedTurn, drainIncrement_erases] using ih (start + 1) final

/-- Raw result erasure preserves every original success and failure. -/
theorem drainAuditRun_original (upTo : Option PeerId) (entry : World) :
    drainEraseRaw (drainAuditRun upTo 4096 entry) =
      (drainHandshakeSendWq upTo).run entry := by
  rw [← drain_source]
  unfold drainSource
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact drainAuditRun_range upTo 4096 0 entry

theorem projectDrain_erases (result : DrainRaw) :
    eraseDrainOutcome (projectDrain result) = observeResult (drainEraseRaw result) := by
  cases result <;> rfl

/-- Inspection returns its datum at the entry state. Erasing the datum, rather
than dropping the inspection call, gives the inspected original outcome. -/
theorem observedDrain_source (upTo : Option PeerId) :
    (do let out ← observedDrain upTo; pure (eraseDrainOutcome out)) =
      inspect (drainHandshakeSendWq upTo) := by
  funext entry
  change Except.ok (eraseDrainOutcome (projectDrain (drainAuditRun upTo 4096 entry)), entry) =
    Except.ok (observeResult ((drainHandshakeSendWq upTo).run entry), entry)
  rw [projectDrain_erases, drainAuditRun_original]

end Leanux.Proofs.WG.Progress
