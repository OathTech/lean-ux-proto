import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedFixtureScopeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecycleEnvironmentDispatch

/-! All five lifecycle callback families use their concrete source points:
fixture-scoped staging and keepalive, work drain, counted purge and peer
repayment. The original stronger deletion input remains in the caller proof. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Concrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev History := List Event

def workPoints : WorkService.Points.ChildPoints :=
  Service.Expanded.workPoints (ProtocolSend.workPoints (fun _ _ _ _ _=>False))

def points : Points.ChildPoints := fun _ _ token w h u middle=>match token with
  | .family (.staging pid)=>FixtureScope.Point (.interfaceOpen pid .staging)
      (Driver.stagingObserved hooks pid) (StagingExpanded.RootPoint pid) w h u middle
  | .family (.keepalive pid)=>FixtureScope.Point (.interfaceOpen pid .keepalive)
      (Driver.keepaliveObserved hooks pid) (KeepaliveExpanded.RootPoint pid) w h u middle
  | .family (.drain upTo)=>WorkService.Points.RootPoint workPoints (.drain upTo) w h u middle
  | .family (.purge pid)=>Timer.Points.Purge.Point pid w h u middle
  | .family (.release peer)=>PeerRetirement.Points.NativePoints peer w h u middle

variable {Good : History → World → Prop}

noncomputable def workChildren
    (accountGood : ∀h w,Points.Account h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w) :
    WorkService.Points.ChildContracts workPoints workPoints Good :=
  WorkService.ServiceComposition.workChildren acceptPeer (ProtocolSend.senderContract accountGood acceptPeer)

noncomputable def stagingContract
    (accountGood : ∀h w,Points.Account h w → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (pid : PeerId) : Points.ChildSourceContract points points Good (.family (.staging pid)) where
  remainder:=fun _ _ _ _ point=>FixtureScope.remainder (fun _ _ _ _ p=>p.residual) point
  continuation:=fun _ _ _ _ point=>FixtureScope.remainder_run (fun _ _ _ _ p=>p.residual) point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    apply point.safe (fun _ _ before=>accountGood _ _ before.1)
      (CompleteProduct.state (CompleteProduct.staging pid)) ?_ before
    intro w h u middle before point
    obtain ⟨ledger,account⟩:=before.1
    exact acceptStaging ledger _ _ (point.evidence account)

noncomputable def keepaliveContract
    (accountGood : ∀h w,Points.Account h w → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (pid : PeerId) : Points.ChildSourceContract points points Good (.family (.keepalive pid)) where
  remainder:=fun _ _ _ _ point=>FixtureScope.remainder (fun _ _ _ _ p=>p.residual) point
  continuation:=fun _ _ _ _ point=>FixtureScope.remainder_run (fun _ _ _ _ p=>p.residual) point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    apply point.safe (fun _ _ before=>accountGood _ _ before.1)
      (CompleteProduct.state (CompleteProduct.keepalive pid)) ?_ before
    intro w h u middle before point
    obtain ⟨ledger,account⟩:=before.1
    exact acceptKeepalive ledger pid w h u middle (point.evidence account)

noncomputable def drainContract
    (accountGood : ∀h w,Points.Account h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (upTo : Option PeerId) : Points.ChildSourceContract points points Good (.family (.drain upTo)) where
  remainder:=WorkService.ServiceComposition.remainder (.drain upTo) (workChildren accountGood acceptPeer)
  continuation:=fun _ _ _ _ point=>WorkService.ServiceComposition.remainder_run
    (.drain upTo) (workChildren accountGood acceptPeer) point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    obtain ⟨site,point⟩:=point
    exact point.safe accountGood (workChildren accountGood acceptPeer) before

noncomputable def purgeContract
    (accountGood : ∀h w,Points.Account h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (pid : PeerId) : Points.ChildSourceContract points points Good (.family (.purge pid)) where
  remainder:=fun _ _ _ _ point=>Timer.Points.Purge.remainder point
  continuation:=fun _ _ _ _ point=>Timer.Points.Purge.point_continuation point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    rcases Timer.Points.Purge.point_evidence before point with accounted | pending
    · exact accountGood _ _ accounted
    · exact pendingGood _ _ pending

noncomputable def releaseContract
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (peer : Option PeerId) : Points.ChildSourceContract points points Good (.family (.release peer)) where
  remainder:=fun _ _ _ _ point=>PeerRetirement.Points.continuation point
  continuation:=fun _ _ _ _ point=>PeerRetirement.Points.continuation_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    obtain ⟨ledger,account⟩:=before
    exact acceptPeer ledger _ _ (PeerRetirement.Points.native_evidence account point)

/-- Every declared lifecycle callback cut retains its actual packet account
or the precise pending receipt, without an incoming callback-source contract.
Deletion still requires its original stronger native entry and guard. -/
noncomputable def children
    (accountGood : ∀h w,Points.Account h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u) :
    Points.ChildContracts points points Good where
  staging:=stagingContract accountGood acceptStaging
  keepalive:=keepaliveContract accountGood acceptKeepalive
  drain:=drainContract accountGood acceptPeer
  purge:=purgeContract accountGood pendingGood
  release:=releaseContract acceptPeer

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Concrete
