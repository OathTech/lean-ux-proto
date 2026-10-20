import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigConcretePoints

/-! Configuration's dispatch contract is supplied by its original source
witness. It introduces no incoming whole-configuration callback premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

def dispatchPoints (other : Dispatch.Points.ChildPoints) : Dispatch.Points.ChildPoints :=
  fun _ _ token w h u middle=>match token with
    | .family (.config attrs)=>RootPoint attrs w h u middle
    | token=>other _ _ token w h u middle

variable {nativeService insideService : Service.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeOther insideOther : Dispatch.Points.ChildPoints} {Good : History → World → Prop}

noncomputable def configContract
    (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (attrs : DeviceAttrs) : Dispatch.Points.ChildSourceContract
      (TrafficConcrete.serviceDispatch nativeService nativeNapi (dispatchPoints nativeOther))
      (TrafficConcrete.serviceDispatch insideService insideNapi (dispatchPoints insideOther)) Good (.family (.config attrs)) where
  remainder:=fun _ _ _ _ point=>remainder (attrs:=attrs) point
  continuation:=fun _ _ _ _ point=>remainder_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    obtain ⟨site,point⟩:=point
    exact point.safe accountGood pendingGood acceptPeer acceptStaging acceptKeepalive before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
