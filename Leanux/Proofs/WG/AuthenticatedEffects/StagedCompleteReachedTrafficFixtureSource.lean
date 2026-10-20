import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTrafficConcreteFrames

/-! A batch transmit keeps the fixture token across the same routed child.
The child point cannot restart the fixture wrapper at its interior world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete.Fixture
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal Driver

def entered (input : RoutedTransmit.Input) : PrefixM Event Nat :=
  Xmit.entered input.family input.address input.packets input.mtu

def action (input : RoutedTransmit.Input) : PrefixM Event Int :=
  fixtureTransmit input.family input.address input.packets input.mtu

def afterBody (token : Nat) (ret : Int) : PrefixM Event Int := do
  XmitConcrete.leave token
  pure ret

theorem source (input : RoutedTransmit.Input) :
    action input=(entered input >>= fun token=>RoutedTransmit.action input >>= afterBody token) := by
  unfold action fixtureTransmit FixtureEffects.runWith
  simp only [liftWGObserver_bind,liftWGObserver_pure]
  rfl

inductive Point (input : RoutedTransmit.Input) (w : World) (h : History) : World → History → Prop where
  | entry : Point input w h w h
  | routed (marked : runPrefix (entered input) w h=(.ok (token,u),middle))
      (point : RoutedTransmit.Point input u middle v last) : Point input w h v last
  | returned (performed : runPrefix (action input) w h=(.ok (value,u),middle)) : Point input w h u middle

theorem Point.remaining (point : Point input w h u middle) :
    ∃remaining,runPrefix (action input) w h=runPrefix remaining u middle := by
  cases point with
  | entry=>exact ⟨_,rfl⟩
  | routed marked point=>
      rw [source,runPrefix_bind,marked]
      exact ⟨RoutedTransmit.remainder point >>= afterBody _,
        Scheduler.bind_run_equal _ (RoutedTransmit.remainder_run point)⟩
  | returned performed=>exact ⟨pure _,performed⟩

noncomputable def remainder (point : Point input w h u middle) : PrefixM Event Int :=
  Classical.choose point.remaining

theorem remainder_run (point : Point input w h u middle) :
    runPrefix (action input) w h=runPrefix (remainder point) u middle :=
  Classical.choose_spec point.remaining

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete.Fixture
