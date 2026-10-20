import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPrepareMetadataSource
import Leanux.Proofs.WG.Lifetimes.LoopbackAccess

/-! Socket adapter points expose WG reads, the isolated routing computation,
its write-back, and each loopback metadata update. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

macro "socket_metadata_step" : tactic => `(tactic| first
  | (metadata_source_head modify; apply Shape.access; apply Access.Shape.write;
      exact KeyFrames.world _ (fun _ => rfl))
  | receive_metadata_step)

def routeAdapterBody (body : Net.M α) : WG.M α := do
  let g ← (get : WG.M WGWorld)
  let initial : Net.State := {toRouting:=g.routing, wg0:=g.dev.map fun d => {running:=d.running,inet4Dev:=d.inet4Dev}}
  let pair ← (monadLift (body.run initial) : WG.M (α × Net.State))
  modify fun w => {w with routing:=pair.2.toRouting}
  pure pair.1

theorem routeAdapter_source (body : Net.M α) : liftRouting body = routeAdapterBody body := by
  funext g ambient
  let initial : Net.State := {toRouting:=g.routing, wg0:=g.dev.map fun d => {running:=d.running,inet4Dev:=d.inet4Dev}}
  change ((liftRouting body).run g).run ambient = ((routeAdapterBody body).run g).run ambient
  rw [liftRouting_run]
  cases performed : (body.run initial).run ambient <;>
    simp [routeAdapterBody,initial,StateT.run_bind] at performed ⊢ <;> rw [performed] <;> rfl

noncomputable def routeAdapterShape (body : Net.M α) : Shape (liftRouting body) := by
  rw [routeAdapter_source]
  unfold routeAdapterBody
  repeat' socket_metadata_step

noncomputable def routingReadShape : Shape (getRouting : WG.M Net.Routing) := by
  unfold getRouting
  exact routeAdapterShape _

noncomputable def socketPortShape (family : Nat) : Shape (socketPort family) := by
  unfold socketPort
  repeat' socket_metadata_step

noncomputable def loopbackRaiseShape : Shape raiseLoopbackRx := by
  unfold raiseLoopbackRx
  repeat' socket_metadata_step

noncomputable def loopbackFinishShape : Shape loopbackFinish := by
  unfold loopbackFinish
  repeat' socket_metadata_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerMetadata
