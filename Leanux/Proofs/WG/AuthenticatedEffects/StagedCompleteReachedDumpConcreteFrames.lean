import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDumpConcreteSource

/-! The actual dump source is ordinary for the packet account. Cursor release
is a concrete counted callback; header and walk interiors use fixed metadata trees. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DumpConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Lifecycle.Points

theorem root_framed (root : Root) (before : Account h w) :
    Framed (canonical root).1 w h := (canonical root).2.framed before

def RootPoint (root : Root) (w : World) (h : List Event) (u : World) (middle : List Event) : Prop :=
  ∃site,Point Lifecycle.Concrete.points (canonical root).1 w h site u middle

variable {Good : List Event → World → Prop}

theorem root_safe (root : Root) (accountGood : ∀h w,Account h w → Good h w)
    (children : ChildContracts Lifecycle.Concrete.points Lifecycle.Concrete.points Good)
    (before : Account h w) (point : RootPoint root w h u middle) : Good middle u := by
  obtain ⟨site,point⟩:=point
  exact point.safe accountGood children (root_framed root before)

theorem root_remainder (root : Root)
    (children : ChildContracts Lifecycle.Concrete.points Lifecycle.Concrete.points Good)
    (point : RootPoint root w h u middle) :
    ∃rest,(∃site,Residual children (canonical root).1 w h site u middle rest) ∧
      runPrefix (liftWGObserver root.action) w h=runPrefix rest u middle := by
  obtain ⟨site,point⟩:=point
  obtain ⟨rest,residual⟩:=point.residual children
  exact ⟨rest,⟨site,residual⟩,residual.run⟩

noncomputable def remainder (root : Root)
    (children : ChildContracts Lifecycle.Concrete.points Lifecycle.Concrete.points Good)
    (w : World) (h : List Event) (u : World) (middle : List Event)
    (point : RootPoint root w h u middle) : PrefixM Event root.Result :=
  Classical.choose (root_remainder root children point)

theorem remainder_run (root : Root)
    (children : ChildContracts Lifecycle.Concrete.points Lifecycle.Concrete.points Good)
    (point : RootPoint root w h u middle) :
    runPrefix (liftWGObserver root.action) w h=runPrefix (remainder root children w h u middle point) u middle :=
  (Classical.choose_spec (root_remainder root children point)).2

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DumpConcrete
