import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServicePointJoin
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchPointComposition

/-! Share the actual idle and delivery source roots with dispatch. All other
families retain their own point relations and entry conditions, including the
stronger deletion entry. The remaining contracts are explicit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Composition
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev History := List Event

def dispatchPoints (service : Points.ChildPoints) (other : Dispatch.Points.ChildPoints) :
    Dispatch.Points.ChildPoints := fun α action token w h u middle => match token with
  | .family .idle => Points.RootPoints service .idle w h u middle
  | .family .delivery => Points.RootPoints service .delivery w h u middle
  | token => other α action token w h u middle

variable {native inside : Points.ChildPoints}
  {nativeOther insideOther : Dispatch.Points.ChildPoints} {Good : History → World → Prop}

structure DispatchOther (native inside : Points.ChildPoints)
    (nativeOther insideOther : Dispatch.Points.ChildPoints) (Good : History → World → Prop) where
  config : ∀attrs,Dispatch.Points.ChildSourceContract (dispatchPoints native nativeOther) (dispatchPoints inside insideOther) Good (.family (.config attrs))
  create : Dispatch.Points.ChildSourceContract (dispatchPoints native nativeOther) (dispatchPoints inside insideOther) Good (.family .create)
  delete : Dispatch.Points.ChildSourceContract (dispatchPoints native nativeOther) (dispatchPoints inside insideOther) Good (.family .delete)
  openDevice : Dispatch.Points.ChildSourceContract (dispatchPoints native nativeOther) (dispatchPoints inside insideOther) Good (.family .open)
  down : Dispatch.Points.ChildSourceContract (dispatchPoints native nativeOther) (dispatchPoints inside insideOther) Good (.family .down)
  transmit : ∀family addr payload opts,Dispatch.Points.ChildSourceContract (dispatchPoints native nativeOther) (dispatchPoints inside insideOther) Good (.family (.transmit family addr payload opts))
  receive : ∀family port message tos ll dest,Dispatch.Points.ChildSourceContract (dispatchPoints native nativeOther) (dispatchPoints inside insideOther) Good (.family (.receive family port message tos ll dest))
  flood : ∀count port family messages,Dispatch.Points.ChildSourceContract (dispatchPoints native nativeOther) (dispatchPoints inside insideOther) Good (.family (.flood count port family messages))
  batch : ∀items,Dispatch.Points.ChildSourceContract (dispatchPoints native nativeOther) (dispatchPoints inside insideOther) Good (.family (.batch items))
  dumpDevice : ∀ref,Dispatch.Points.ChildSourceContract (dispatchPoints native nativeOther) (dispatchPoints inside insideOther) Good (.family (.dumpDevice ref))
  dumpStart : ∀fd ref,Dispatch.Points.ChildSourceContract (dispatchPoints native nativeOther) (dispatchPoints inside insideOther) Good (.family (.dumpStart fd ref))
  dumpReceive : ∀fd,Dispatch.Points.ChildSourceContract (dispatchPoints native nativeOther) (dispatchPoints inside insideOther) Good (.family (.dumpReceive fd))

noncomputable def dispatchIdle
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (children : Points.ChildContracts native inside Good) :
    Dispatch.Points.ChildSourceContract (dispatchPoints native nativeOther)
      (dispatchPoints inside insideOther) Good (.family .idle) where
  remainder := Points.remainder .idle children
  continuation := fun _ _ _ _ point => Points.remainder_run .idle children point
  coverage := fun _ _ _ _ point => Points.root_coverage .idle children point
  safe := fun _ _ _ _ before point => Points.root_safe .idle carrierGood children before point

noncomputable def dispatchDelivery
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (children : Points.ChildContracts native inside Good) :
    Dispatch.Points.ChildSourceContract (dispatchPoints native nativeOther)
      (dispatchPoints inside insideOther) Good (.family .delivery) where
  remainder := Points.remainder .delivery children
  continuation := fun _ _ _ _ point => Points.remainder_run .delivery children point
  coverage := fun _ _ _ _ point => Points.root_coverage .delivery children point
  safe := fun _ _ _ _ before point => Points.root_safe .delivery carrierGood children before point

noncomputable def dispatchChildren
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (children : Points.ChildContracts native inside Good)
    (other : DispatchOther native inside nativeOther insideOther Good) :
    Dispatch.Points.ChildContracts (dispatchPoints native nativeOther)
      (dispatchPoints inside insideOther) Good where
  config := other.config
  create := other.create
  delete := other.delete
  openDevice := other.openDevice
  down := other.down
  transmit := other.transmit
  receive := other.receive
  flood := other.flood
  batch := other.batch
  dumpDevice := other.dumpDevice
  dumpStart := other.dumpStart
  dumpReceive := other.dumpReceive
  idle := dispatchIdle carrierGood children
  delivery := dispatchDelivery carrierGood children

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Service.Composition
