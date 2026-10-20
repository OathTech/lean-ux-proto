import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTrafficConcreteChildren

/-! Three traffic dispatch contracts come from their fixed source points.
Only configuration remains an incoming dispatch-family contract here. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

def dispatchPoints (service : Service.Points.ChildPoints) (napi : Napi.Points.ChildPoints)
    (other : Dispatch.Points.ChildPoints) : Dispatch.Points.ChildPoints :=
  fun _ _ token w h u middle=>match token with
    | .family (.receive family port msg tos ll dest)=>RootPoint service napi (.receive family port msg tos ll dest) w h u middle
    | .family (.flood count port family messages)=>RootPoint service napi (.flood count port family messages) w h u middle
    | .family (.batch items)=>RootPoint service napi (.batch items) w h u middle
    | token=>other _ _ token w h u middle

abbrev serviceDispatch (service : Service.Points.ChildPoints) (napi : Napi.Points.ChildPoints)
    (other : Dispatch.Points.ChildPoints) :=
  XmitConcrete.serviceDispatch service (dispatchPoints service napi other)

variable {nativeService insideService : Service.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeOther insideOther : Dispatch.Points.ChildPoints} {Good : History → World → Prop}

noncomputable def dispatchContracts
    (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (services : Service.Points.ChildContracts nativeService insideService Good)
    (polls : Napi.Points.ChildContracts nativeNapi insideNapi Good)
    (config : ∀attrs,Dispatch.Points.ChildSourceContract
      (serviceDispatch nativeService nativeNapi nativeOther) (serviceDispatch insideService insideNapi insideOther)
      Good (.family (.config attrs))) :
    XmitConcrete.DispatchOther nativeService insideService
      (dispatchPoints nativeService nativeNapi nativeOther) (dispatchPoints insideService insideNapi insideOther) Good where
  config:=config
  receive:=fun family port msg tos ll dest=>{
    remainder:=fun _ _ _ _ point=>remainder (root:=.receive family port msg tos ll dest) services polls point
    continuation:=fun _ _ _ _ point=>remainder_run services polls point
    coverage:=fun _ _ _ _ point=>by
      obtain ⟨site,point⟩:=point
      exact ⟨site,point.coverage services polls⟩
    safe:=fun _ _ _ _ before point=>root_safe accountGood acceptStaging acceptPeer services polls before point}
  flood:=fun count port family messages=>{
    remainder:=fun _ _ _ _ point=>remainder (root:=.flood count port family messages) services polls point
    continuation:=fun _ _ _ _ point=>remainder_run services polls point
    coverage:=fun _ _ _ _ point=>by
      obtain ⟨site,point⟩:=point
      exact ⟨site,point.coverage services polls⟩
    safe:=fun _ _ _ _ before point=>root_safe accountGood acceptStaging acceptPeer services polls before point}
  batch:=fun items=>{
    remainder:=fun _ _ _ _ point=>remainder (root:=.batch items) services polls point
    continuation:=fun _ _ _ _ point=>remainder_run services polls point
    coverage:=fun _ _ _ _ point=>by
      obtain ⟨site,point⟩:=point
      exact ⟨site,point.coverage services polls⟩
    safe:=fun _ _ _ _ before point=>root_safe accountGood acceptStaging acceptPeer services polls before point}

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete
