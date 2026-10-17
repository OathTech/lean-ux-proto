import Leanux.Proofs.WG.Progress.DrainAuditSource
import Leanux.Proofs.WG.Progress.DrainProductModel

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Progress.Product
open Leanux Leanux.WG

abbrev DrainRaw := Except DrainFailure (DrainSuccess × World)

def drainIncrement : DrainRaw → DrainRaw
  | .error failure => .error {failure with attempts := failure.attempts + 1}
  | .ok (success, final) => .ok ({success with attempts := success.attempts + 1}, final)

/-- Map actual native execution through liftWG's exact product update. The
initial product supplies every untouched component; no default state is built. -/
def drainAuditRun (upTo : Option PeerId) (fuel : Nat) (entry : World) : DrainRaw :=
  (Progress.drainAuditRun upTo fuel entry.wg entry.ambient).map
    (fun (success, final, ambient) => (success, {entry with wg := final, ambient}))

def drainEraseRaw : DrainRaw → Except Stop (Unit × World)
  | .error failure => .error failure.error
  | .ok (_, final) => .ok ((), final)

def projectDrain : DrainRaw → DrainOutcome
  | .error failure => .error failure
  | .ok (success, final) => .ok (success, Campaign2.Product.snapshot final)

def observedDrain (upTo : Option PeerId) : Leanux.M DrainOutcome := fun entry =>
  .ok (projectDrain (drainAuditRun upTo 4096 entry), entry)

theorem drainIncrement_erases (result : DrainRaw) :
    drainEraseRaw (drainIncrement result) = drainEraseRaw result := by
  cases result <;> rfl

theorem drainAuditRun_range (upTo : Option PeerId) (fuel start : Nat) (entry : World) :
    drainEraseRaw (drainAuditRun upTo fuel entry) =
      (liftWG (do let state ← forIn (List.range' start fuel) (none, ()) (drainTurn upTo)
                  drainFinish state)).run entry := by
  have mapped (result : Progress.DrainRaw) :
      drainEraseRaw (result.map (fun (success, final, ambient) =>
        (success, {entry with wg := final, ambient}))) =
      (Progress.drainEraseRaw result >>= fun ((value, final), ambient) =>
        Except.ok (value, {entry with wg := final, ambient})) := by
    cases result <;> rfl
  unfold drainAuditRun
  rw [mapped, Progress.drainAuditRun_range upTo fuel start]
  rfl

theorem drainAuditRun_original (upTo : Option PeerId) (entry : World) :
    drainEraseRaw (drainAuditRun upTo 4096 entry) =
      (liftWG (drainHandshakeSendWq upTo)).run entry := by
  rw [← drain_source]
  unfold drainSource
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact drainAuditRun_range upTo 4096 0 entry

theorem projectDrain_erases (result : DrainRaw) :
    eraseDrainOutcome (projectDrain result) = Campaign2.Product.observeResult (drainEraseRaw result) := by
  cases result <;> rfl

theorem observedDrain_source (upTo : Option PeerId) :
    (do let out ← observedDrain upTo; pure (eraseDrainOutcome out)) =
      Campaign2.Product.inspect (liftWG (drainHandshakeSendWq upTo)) := by
  funext entry
  change Except.ok (eraseDrainOutcome (projectDrain (drainAuditRun upTo 4096 entry)), entry) =
    Except.ok (Campaign2.Product.observeResult ((liftWG (drainHandshakeSendWq upTo)).run entry), entry)
  rw [projectDrain_erases, drainAuditRun_original]

end Leanux.Proofs.WG.Progress.Product
