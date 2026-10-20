import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTrafficFixtureSource

/-! Actual fixture entry derives the routed child's account; the original
scope token remains in the source continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete.Fixture
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
variable {Good : History → World → Prop}

/-- Security: fixture-wrapped batch transmit retains its original routed
packet lineage and pending staging/repayment evidence through scope exit. -/
theorem Point.safe
    (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (before : CompleteProduct.Carrier h w) (point : Point input w h u middle) : Good middle u := by
  cases point with
  | entry=>exact accountGood _ _ before.1
  | routed marked point=>
      have start:=Xmit.normal (Xmit.entered_checked input.family input.address input.packets input.mtu) before marked
      exact point.safe accountGood acceptStaging acceptPeer start.1
  | returned performed=>
      exact accountGood _ _ (Xmit.normal (fixture_checked input.family input.address input.packets input.mtu) before performed).1

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete.Fixture
