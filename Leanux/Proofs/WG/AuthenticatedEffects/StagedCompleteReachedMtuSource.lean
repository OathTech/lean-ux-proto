import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProductScalarFrames

/-! The MTU call retains its range checks, scalar write, routing notifiers
and descriptor wrapper. No packet-store field is included in the scalar mask. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductScalar
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

noncomputable def destroyShape : ProductStore.Shape Env.inetdevDestroy := by
  unfold Env.inetdevDestroy
  repeat' control_store_step

def nativeMtuShape (value : Int) : Shape (liftWG (WG.setMtu value)) := by
  by_cases low : value < 0
  · simp only [WG.setMtu,low,ite_true]
    exact .pure _
  · by_cases high : value > MAX_MTU
    · simp only [WG.setMtu,low,high,ite_false,ite_true]
      exact .pure _
    · simp only [WG.setMtu,low,high,ite_false]
      rw [liftWG_bind]
      apply Shape.bind ?_ (fun _=>.pure _)
      exact .write _ (by
        intro w
        cases device : w.wg.dev <;>
          simp [envScalarWGView,wgStoreView,envScalarDevice,device])

macro "mtu_source_step" : tactic => `(tactic| first
  | exact Shape.pure _
  | exact nativeMtuShape _
  | exact Shape.stored destroyShape
  | exact Shape.stored (ProductStore.fsShape _)
  | exact Shape.stored (ProductStore.routeShape _)
  | exact Shape.stored (.reading (.wg .read))
  | exact Shape.stored (.reading (.wg ReadAccess.deviceShape))
  | exact Shape.stored (.ambient (AmbientM.skipCut _))
  | exact Shape.stored (.ambient (AmbientM.unsupported _))
  | apply Shape.bind
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

noncomputable def mtuShape (value : Nat) : Shape (Env.setMtu value) := by
  unfold Env.setMtu
  repeat' mtu_source_step

noncomputable def callShape (value : Nat) : Shape (Leanux.dispatch (.wgSetMtu value)) := by
  unfold Leanux.dispatch Leanux.socketCallOn
  repeat' first | exact mtuShape _ | mtu_source_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProductScalar
