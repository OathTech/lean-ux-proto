import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingExpandedEvidence
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumePointContract

/-! Receive consumption's staging child uses the concrete expanded source
family. Its exact native continuation writes back only WG and ambient state;
all other product-world fields retain the caller's original values. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingExpanded
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

inductive RootPoint (pid : PeerId) (w : World) (h : List Event) : World → List Event → Prop where
  | source (point : Point pid w.wg w.ambient h v b last) :
      RootPoint pid w h {w with wg:=v,ambient:=b} last

theorem RootPoint.evidence (point : RootPoint pid w h u middle)
    (before : CompleteCarrier.Accounted h ledger debts locals w.wg) :
    Evidence ledger debts locals middle u.wg u.ambient := by
  cases point with
  | source point=>exact point.evidence before

theorem RootPoint.residual (point : RootPoint pid w h u middle) :
    ∃remaining,runPrefix (liftWGObserver (Driver.stagingObserved hooks pid)) w h=
      runPrefix remaining u middle := by
  cases point with
  | source point=>exact ⟨_,StagingComposition.lift_residual w (remainder_run point)⟩

noncomputable def rootRemainder (pid : PeerId) (w : World) (h : List Event)
    (u : World) (middle : List Event) (point : RootPoint pid w h u middle) : PrefixM Event Unit :=
  Classical.choose point.residual

theorem root_remainder_run (point : RootPoint pid w h u middle) :
    runPrefix (liftWGObserver (Driver.stagingObserved hooks pid)) w h=
      runPrefix (rootRemainder pid w h u middle point) u middle := Classical.choose_spec point.residual

def consumePoints (other : Consume.Points.ChildPoints) : Consume.Points.ChildPoints :=
  fun token w h u middle=>match token with
  | .staging pid=>RootPoint pid w h u middle
  | token=>other token w h u middle

/-- The actual receive-side staging entry derives every declared cut's
conservation evidence and continuation without a staging-child contract. -/
noncomputable def consume_contract {native inside : Consume.Points.ChildPoints}
    {Good : List Event → World → Prop}
    (accept : ∀ledger h w,Evidence ledger [] [] h w.wg w.ambient → Good h w) (pid : PeerId) :
    Consume.Points.ChildSourceContract (consumePoints native) (consumePoints inside) Good (.staging pid) where
  remainder:=rootRemainder pid
  continuation:=fun _ _ _ _ point=>root_remainder_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    obtain ⟨ledger,account⟩:=before
    exact accept ledger middle u (point.evidence account)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingExpanded
