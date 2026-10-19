import Leanux.Proofs.Framing.Batch
import Leanux.Env

/-! The landed refill bound and pending-device queries read scheduler inputs
without changing a modeled store. Their ambient bookkeeping is outside the
store projection, as for the existing occupancy and consistency frames. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Lifetimes

private theorem device_read : SameProductStore (Leanux.liftWG WG.getDev) := by
  apply liftWG_sameProductStore
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient d v ambient' run
  cases device : w.dev <;> simp [WG.getDev,device,invariant,AmbientM.invariant] at run
  · cases run
  · rcases run with ⟨⟨_,rfl⟩,_⟩
    rfl

private theorem ambient_read (body : AmbientM α) :
    SameProductStore (monadLift body : Leanux.M α) :=
  fun initial => productAmbient_spec body (fun w => productStoreView w = initial)
    (fun _ _ before => before)

/-- The refill allowance depends on actual remaining records and pending
polls; reading it preserves every modeled store. -/
theorem activationRefills_sameKernel : SameProductStore Env.Activation.refills := by
  unfold Env.Activation.refills
  apply SameView.bind device_read
  intro device
  exact SameView.bind (ambient_read AmbientM.recordsLeft) (fun _ => SameView.pure _ _)

/-- An empty ring can still dispatch its recorded pending unit; the dispatch
eligibility query itself changes no modeled store. -/
theorem pendingDevice_sameKernel (worker : Worker) (queued : Bool) :
    SameProductStore (Env.pendingDevice worker queued) := by
  unfold Env.pendingDevice
  exact SameView.bind (ambient_read (get : AmbientM Ambient)) (fun _ => SameView.pure _ _)

/-- Reading pending device units for the completion guard changes no store. -/
theorem pendingDeviceUnits_sameKernel :
    SameProductStore (pendingDeviceUnits : Leanux.M (List Worker)) :=
  ambient_read AmbientM.pendingDeviceUnits

/-- Completion refuses a pending device unit as well as queued work or NAPI.
Every successful check preserves the modeled stores. -/
theorem requireDrained_sameKernel (what : String) (queues : List Bool) :
    SameProductStore (Env.requireDrained what queues) := by
  have tail : SameProductStore (do
      let d ← Leanux.liftWG getDev
      if d.peers.toList.any (·.2.napiScheduled) then
        invariant "a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)" : Leanux.M Unit) := by
    apply SameView.bind device_read
    intro device
    split
    · exact ambient_read (AmbientM.invariant _)
    · exact SameView.pure _ _
  have checked : SameProductStore (do
      if let worker :: _ ← (pendingDeviceUnits : Leanux.M (List Worker)) then
        unsupported s!"{worker.symbol} is pending at the end of the wait (the dispatch its requeue causes has no section in the records)"
      let d ← Leanux.liftWG getDev
      if d.peers.toList.any (·.2.napiScheduled) then
        invariant "a NAPI poll pending after the decrypt worker (its ring poll runs the softirq)" : Leanux.M Unit) := by
    apply SameView.bind pendingDeviceUnits_sameKernel
    intro workers
    cases workers with
    | nil => exact tail
    | cons worker rest => exact SameView.bind (ambient_read (AmbientM.unsupported _)) (fun _ => tail)
  unfold Env.requireDrained
  split
  · exact SameView.bind (ambient_read (AmbientM.unsupported _)) (fun _ => checked)
  · exact checked

end Leanux.Proofs.Framing
