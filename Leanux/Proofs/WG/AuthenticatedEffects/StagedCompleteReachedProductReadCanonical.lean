import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProductReadFrames

/-! Literal read-only scheduler and service guards. Consistency trials are
evaluated on a saved value of World, so only their Boolean or Stop escapes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductRead
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

macro "product_read_step" : tactic => `(tactic| first
  | exact Shape.pure _
  | exact Shape.read
  | exact Shape.ambient (get : AmbientM Ambient)
  | exact Shape.ambient AmbientM.recordsLeft
  | exact Shape.ambient (AmbientM.invariant _)
  | exact Shape.ambient (AmbientM.unsupported _)
  | exact Shape.ambient (throw _)
  | exact Shape.ambient _
  | exact Shape.wg ReadAccess.deviceShape
  | exact Shape.wg (ReadAccess.peerShape _)
  | exact Shape.wg ReadAccess.Shape.read
  | exact Shape.packet _
  | apply Shape.bind
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

noncomputable def environmentShape : Shape getEnv := by
  unfold getEnv
  repeat' product_read_step

/-- The read-only Net action returns its input routing component. Its
adapter's write-back therefore reduces to the incoming product world. -/
noncomputable def routingShape : Shape (getRouting : Leanux.M Net.Routing) := by
  change Shape (do let w ← (get : Leanux.M World); pure w.wg.routing)
  exact .bind .read (fun _=>.pure _)

noncomputable def occupancyShape (a : Activation) : Shape (Env.Activation.occupancy a) := by
  unfold Env.Activation.occupancy
  repeat' product_read_step

noncomputable def refillsShape : Shape Env.Activation.refills := by
  unfold Env.Activation.refills
  repeat' product_read_step

noncomputable def pendingShape (worker : Worker) (queued : Bool) : Shape (Env.pendingDevice worker queued) := by
  unfold Env.pendingDevice
  repeat' product_read_step

noncomputable def napiShape (next : Option Nat) : Shape (Lifetimes.pendingNapi next) := by
  unfold Lifetimes.pendingNapi
  repeat' product_read_step

noncomputable def workShape (a : Activation) : Shape (Env.Activation.hasWork a) := by
  unfold Env.Activation.hasWork
  repeat' product_read_step

noncomputable def consistentShape (a : Activation) : Shape (Env.Activation.consistent a) := by
  unfold Env.Activation.consistent
  repeat' product_read_step

noncomputable def filterAuxShape (body : α → Leanux.M Bool) (sources : ∀ x, Shape (body x))
    (xs acc : List α) : Shape (List.filterAuxM body xs acc) := by
  induction xs generalizing acc with
  | nil => exact .pure _
  | cons x xs ih => exact .bind (sources x) (fun b=>ih (cond b (x::acc) acc))

noncomputable def trialsShape (active : List Activation) : Shape (active.filterM Env.Activation.consistent) :=
  .bind (filterAuxShape _ consistentShape active []) (fun xs=>.pure xs.reverse)

noncomputable def peekShape : Shape Env.peekNextSite := by
  unfold Env.peekNextSite
  repeat' product_read_step

noncomputable def timerWorkerShape (timer : PeerTimer) : Shape (Env.timerWorker timer) := by
  unfold Env.timerWorker
  repeat' product_read_step

noncomputable def laterShape (worker : Worker) (unit : Nat) : Shape (Env.sectionAppearsLater worker unit) := by
  unfold Env.sectionAppearsLater
  repeat' product_read_step

noncomputable def stepShape (expiry : UInt64) : Shape (Env.requireStepComplete expiry) := by
  unfold Env.requireStepComplete
  repeat' product_read_step

noncomputable def dueShape (expiry : UInt64) : Shape (Env.requireNothingDue expiry) := by
  unfold Env.requireNothingDue Env.timerWorker Env.sectionAppearsLater
  repeat' product_read_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductRead
