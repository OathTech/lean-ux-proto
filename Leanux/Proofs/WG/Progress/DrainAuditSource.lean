import Leanux.Proofs.WG.Progress.DrainSelectionSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Campaign2

abbrev DrainRaw := Except DrainFailure (DrainSuccess × WGWorld × Ambient)

def drainIncrement : DrainRaw → DrainRaw
  | .error failure => .error {failure with attempts := failure.attempts + 1}
  | .ok (success, final, ambient) => .ok ({success with attempts := success.attempts + 1}, final, ambient)

def drainAuditRun (upTo : Option PeerId) : Nat → WGWorld → Ambient → DrainRaw
  | 0, _, _ => .error ⟨.ownBudget, .invariant "handshake_send_wq did not drain", 0⟩
  | fuel + 1, entry, ambient =>
    match (drainSelect.run entry).run ambient with
    | .error error => .error ⟨.selection, error, 1⟩
    | .ok ((.drained, selected), inputs) => .ok (⟨.empty, 1⟩, selected, inputs)
    | .ok ((.send pid, selected), inputs) =>
      match ((runFlushedSendWork pid).run selected).run inputs with
      | .error error => .error ⟨.sendWorker pid, error, 1⟩
      | .ok ((_, final), ending) => drainIncrement (drainAuditRun upTo fuel final ending)
    | .ok ((.clear pid, selected), inputs) =>
      match ((runFlushedClearWork pid).run selected).run inputs with
      | .error error => .error ⟨.clearWorker pid, error, 1⟩
      | .ok ((_, final), ending) =>
        if upTo == some pid then .ok (⟨.requestedClear pid, 1⟩, final, ending)
        else drainIncrement (drainAuditRun upTo fuel final ending)

def drainEraseRaw : DrainRaw → Except Stop ((Unit × WGWorld) × Ambient)
  | .error failure => .error failure.error
  | .ok (_, final, ambient) => .ok (((), final), ambient)

def projectDrain : DrainRaw → DrainOutcome
  | .error failure => .error failure
  | .ok (success, final, ambient) => .ok (success, snapshot final ambient)

def observedDrain (upTo : Option PeerId) : WG.M DrainOutcome := fun entry ambient =>
  .ok ((projectDrain (drainAuditRun upTo 4096 entry ambient), entry), ambient)

theorem drainIncrement_erases (result : DrainRaw) :
    drainEraseRaw (drainIncrement result) = drainEraseRaw result := by
  cases result <;> rfl

private theorem except_error_bind {α β : Type} (e : Stop) (f : α → Except Stop β) :
    (Except.error e >>= f) = .error e := rfl

private theorem except_ok_bind {α β : Type} (x : α) (f : α → Except Stop β) :
    (Except.ok x >>= f) = f x := rfl

theorem drainAuditRun_range (upTo : Option PeerId) (fuel start : Nat) (entry : WGWorld) (ambient : Ambient) :
    drainEraseRaw (drainAuditRun upTo fuel entry ambient) =
      ((do let state ← forIn (List.range' start fuel) (none, ()) (drainTurn upTo)
           drainFinish state).run entry).run ambient := by
  induction fuel generalizing start entry ambient with
  | zero => rfl
  | succ fuel ih =>
    simp only [List.range'_succ, List.forIn_cons]
    unfold drainAuditRun
    simp only [drainTurn, bind_assoc]
    cases hs : (drainSelect.run entry).run ambient with
    | error error => simp [hs, StateT.run_bind, except_error_bind, drainEraseRaw]
    | ok found =>
      rcases found with ⟨⟨selected, middle⟩, inputs⟩
      cases selected with
      | drained =>
        simp [hs, StateT.run_bind, StateT.run_pure, except_ok_bind,
          drainSelectedTurn, drainFinish, drainEraseRaw]
        rfl
      | send pid =>
        cases hw : ((runFlushedSendWork pid).run middle).run inputs with
        | error error => simp [hs, hw, StateT.run_bind, StateT.run_map, except_error_bind, except_ok_bind,
            drainSelectedTurn, drainEraseRaw]
        | ok found =>
          rcases found with ⟨⟨_, final⟩, ending⟩
          simpa [hs, hw, StateT.run_bind, StateT.run_pure, StateT.run_map, except_error_bind, except_ok_bind,
            drainSelectedTurn, drainIncrement_erases] using ih (start + 1) final ending
      | clear pid =>
        cases hw : ((runFlushedClearWork pid).run middle).run inputs with
        | error error => simp [hs, hw, StateT.run_bind, except_error_bind, except_ok_bind,
            drainSelectedTurn, drainEraseRaw]
        | ok found =>
          rcases found with ⟨⟨_, final⟩, ending⟩
          by_cases stop : upTo = some pid
          · simp [hs, hw, stop, StateT.run_bind, StateT.run_pure, StateT.run_map, except_ok_bind,
              drainSelectedTurn, drainFinish, drainEraseRaw]
          · simpa [hs, hw, stop, StateT.run_bind, StateT.run_pure, StateT.run_map, except_error_bind, except_ok_bind,
              drainSelectedTurn, drainIncrement_erases] using ih (start + 1) final ending

theorem drainAuditRun_original (upTo : Option PeerId) (entry : WGWorld) (ambient : Ambient) :
    drainEraseRaw (drainAuditRun upTo 4096 entry ambient) =
      ((drainHandshakeSendWq upTo).run entry).run ambient := by
  rw [← drain_source]
  unfold drainSource
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact drainAuditRun_range upTo 4096 0 entry ambient

theorem projectDrain_erases (result : DrainRaw) :
    eraseDrainOutcome (projectDrain result) = observeResult (drainEraseRaw result) := by
  cases result <;> rfl

theorem observedDrain_source (upTo : Option PeerId) :
    (do let out ← observedDrain upTo; pure (eraseDrainOutcome out)) =
      inspect (drainHandshakeSendWq upTo) := by
  funext entry ambient
  change Except.ok ((eraseDrainOutcome (projectDrain (drainAuditRun upTo 4096 entry ambient)), entry), ambient) =
    Except.ok ((observeResult (((drainHandshakeSendWq upTo).run entry).run ambient), entry), ambient)
  rw [projectDrain_erases, drainAuditRun_original]

end Leanux.Proofs.WG.Progress
