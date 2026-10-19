import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionCarrier

/-! Native product leaves may be used only with a frame for the actual sent
buffer. The packet-store projection deliberately cannot discharge this rule. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

theorem product_native (action : Leanux.M α)
    (frame : SameView (fun w : World => w.wg.sent) action) : ProductSafe (liftPrefix action) :=
  viewLiftPrefix_preserves (fun w : World => w.wg.sent) (fun _ _ _ => True.intro)
    (fun _ _ _ same hi => by
      obtain ⟨earlier,kept⟩ := hi
      exact ⟨earlier,by rw [same]; exact kept⟩) frame

theorem carrier_product_native (action : Leanux.M α)
    (frame : SameView (fun w : World => w.wg.sent) action) :
    Deliveries.Carrier.ProductSafe (liftPrefix action) :=
  Deliveries.Carrier.product_native action (product_native action frame)

open Lean Meta Elab Tactic in
elab "emission_product_native_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductSafe do throwError "not a product emission contract"
  let mut action := target.getAppArgs.back!.consumeMData.headBeta
  let expected := wanted.getId.eraseMacroScopes.toString
  for wrapper in [``liftWGObserver, ``liftPrefix, ``liftM, ``MonadLiftT.monadLift,
      ``MonadLift.monadLift, ``liftWG] do
    if action.isAppOf wrapper && expected != wrapper.toString && !wrapper.toString.endsWith ("." ++ expected) then
      action := action.getAppArgs.back!.consumeMData
  let .const actual _ := action.getAppFn | throwError "not a constant-headed source"
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different source head"

open Lean Meta Elab Tactic in
elab "emission_failure_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductSafe do throwError "not a product emission contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``Bind.bind do throwError "not a bind"
  let args := action.getAppArgs
  let head := args[args.size - 2]!.consumeMData.headBeta
  unless head.isAppOf ``liftPrefix do throwError "not a native prefix"
  let native := head.getAppArgs.back!.consumeMData
  let .const actual _ := native.getAppFn | throwError "not a constant-headed leaf"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different leaf"

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
