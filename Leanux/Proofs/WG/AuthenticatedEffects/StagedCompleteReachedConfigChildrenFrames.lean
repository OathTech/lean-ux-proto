import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigChildrenSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigConcreteFrames

/-! Child safety is derived at its actual caller entry. Lifecycle and fixture
contracts are concrete; only the final meaning of accepted evidence is abstract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
variable {Good : History → World → Prop} {family : Family}

theorem Family.Point.safe
    (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (before : CompleteProduct.Carrier h w) (point : family.Point w h u middle) : Good middle u := by
  cases family with
  | release peer=>
      obtain ⟨ledger,account⟩:=before.1
      exact acceptPeer ledger _ _ (PeerRetirement.Points.native_evidence account point)
  | remove peer=>
      obtain ⟨site,point⟩:=point
      exact point.safe accountGood
        (Lifecycle.Concrete.children accountGood pendingGood acceptPeer acceptStaging acceptKeepalive)
        ((remove_ordinary peer).framed before.1)
  | removeAll=>
      obtain ⟨site,point⟩:=point
      exact point.safe accountGood
        (Lifecycle.Concrete.children accountGood pendingGood acceptPeer acceptStaging acceptKeepalive)
        (Lifecycle.Points.remove_all_ordinary.framed before.1)
  | staging trigger pid=>
      apply FixtureScope.Point.safe (fun _ _ before=>accountGood _ _ before.1)
        (CompleteProduct.state (CompleteProduct.staging pid)) ?_ before point
      intro w h u middle before point
      obtain ⟨ledger,account⟩:=before.1
      exact acceptStaging ledger _ _ (point.evidence account)
  | keepalive trigger pid=>
      apply FixtureScope.Point.safe (fun _ _ before=>accountGood _ _ before.1)
        (CompleteProduct.state (CompleteProduct.keepalive pid)) ?_ before point
      intro w h u middle before point
      obtain ⟨ledger,account⟩:=before.1
      exact acceptKeepalive ledger pid w h u middle (point.evidence account)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
