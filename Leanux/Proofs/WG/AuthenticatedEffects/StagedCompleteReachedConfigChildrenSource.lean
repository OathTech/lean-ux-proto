import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigRemovalSource

/-! Configuration children select fixed native point families. Their source
remainders need no account or semantic acceptance premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

def Family.Point (family : Family) (w : World) (h : History) (u : World) (middle : History) : Prop :=
  match family with
  | .release peer=>PeerRetirement.Points.NativePoints peer w h u middle
  | .remove peer=>∃site,Lifecycle.Points.Point Lifecycle.Concrete.points (removeShape peer) w h site u middle
  | .removeAll=>∃site,Lifecycle.Points.Point Lifecycle.Concrete.points Lifecycle.Points.removeAllShape w h site u middle
  | .staging trigger pid=>FixtureScope.Point trigger (Driver.stagingObserved hooks pid) (StagingExpanded.RootPoint pid) w h u middle
  | .keepalive trigger pid=>FixtureScope.Point trigger (Driver.keepaliveObserved hooks pid) (KeepaliveExpanded.RootPoint pid) w h u middle

noncomputable def sourceChildren : Lifecycle.Points.ChildContracts Lifecycle.Concrete.points Lifecycle.Concrete.points (fun _ _=>True) :=
  Lifecycle.Concrete.children (fun _ _ _=>True.intro) (fun _ _ _=>True.intro)
    (fun _ _ _ _=>True.intro) (fun _ _ _ _=>True.intro) (fun _ _ _ _ _ _ _=>True.intro)

theorem Family.Point.remaining {family : Family} (point : family.Point w h u middle) :
    ∃remaining,runPrefix family.action w h=runPrefix remaining u middle := by
  cases family with
  | release peer=>exact ⟨PeerRetirement.Points.continuation point,PeerRetirement.Points.continuation_run point⟩
  | remove peer=>
      obtain ⟨site,point⟩:=point
      obtain ⟨remaining,residual⟩:=point.residual sourceChildren
      exact ⟨remaining,residual.run⟩
  | removeAll=>
      obtain ⟨site,point⟩:=point
      obtain ⟨remaining,residual⟩:=point.residual sourceChildren
      exact ⟨remaining,residual.run⟩
  | staging trigger pid=>exact FixtureScope.Point.remaining (fun _ _ _ _ p=>p.residual) point
  | keepalive trigger pid=>exact FixtureScope.Point.remaining (fun _ _ _ _ p=>p.residual) point

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
