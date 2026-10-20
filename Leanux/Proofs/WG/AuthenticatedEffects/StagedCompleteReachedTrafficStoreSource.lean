import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProductStoreFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProductReadCanonical
import Leanux.Proofs.Framing.Lift

/-! Traffic routing and loopback helpers expose their original reads and
writes. The routing computation runs on a copied component before write-back. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductStore
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def routeBody (body : Net.M α) : Leanux.M α := do
  let w ← (get : Leanux.M World)
  let initial : Net.State := {toRouting:=w.wg.routing,wg0:=w.wg.dev.map fun d=>{running:=d.running,inet4Dev:=d.inet4Dev}}
  let pair ← liftAmbient (body.run initial)
  modify fun v=>{v with wg:={v.wg with routing:=pair.2.toRouting}}
  pure pair.1

theorem route_source (body : Net.M α) : (monadLift body : Leanux.M α)=routeBody body := by
  funext w
  change (liftWG (liftRouting body)).run w=(routeBody body).run w
  rw [liftWG_run,liftRouting_run]
  cases performed : (body.run {toRouting:=w.wg.routing,wg0:=w.wg.dev.map fun d=>{running:=d.running,inet4Dev:=d.inet4Dev}}).run w.ambient <;>
    simp [routeBody,StateT.run_bind,liftAmbient_run,performed,Except.map]

def nativeAmbientShape (body : AmbientM α) : Shape (liftWG (monadLift body : WG.M α)) := by
  change Shape (liftWG (StateT.lift body))
  rw [liftWG_ambient]
  exact .ambient body

macro "traffic_store_step" : tactic => `(tactic| first
  | exact Shape.pure _
  | exact Shape.reading ProductRead.Shape.read
  | exact Shape.reading (.wg .read)
  | exact Shape.reading (.wg ReadAccess.deviceShape)
  | exact Shape.ambient (get : AmbientM Ambient)
  | exact Shape.ambient AmbientM.peekHiddenSite
  | exact Shape.ambient (AmbientM.hidden _)
  | exact Shape.ambient (AmbientM.skipCut _)
  | exact Shape.ambient (AmbientM.invariant _)
  | exact Shape.ambient (AmbientM.unsupported _)
  | exact Shape.ambient (throw _)
  | exact Shape.ambient _
  | exact nativeAmbientShape AmbientM.peekHiddenSite
  | exact nativeAmbientShape (AmbientM.hidden _)
  | exact nativeAmbientShape (AmbientM.skipCut _)
  | exact nativeAmbientShape _
  | exact Shape.write _ (fun _=>rfl)
  | apply Shape.bind
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

noncomputable def routeShape (body : Net.M α) : Shape (monadLift body : Leanux.M α) := by
  rw [route_source]
  unfold routeBody
  repeat' traffic_store_step

noncomputable def loopbackShape (sites : List HiddenSite) (raised : Bool) :
    Shape (liftWG (loopbackSend sites raised)) := by
  unfold loopbackSend raiseLoopbackRx loopbackSoftirq
  simp only [liftWG_bind,liftWG_pure,apply_ite]
  repeat' traffic_store_step

noncomputable def multicastShape (family addr : Nat) : Shape (Env.xmitMulticastLoop family addr) := by
  unfold Env.xmitMulticastLoop
  repeat' first | exact loopbackShape _ _ | traffic_store_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductStore
