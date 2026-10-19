import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedKeepaliveExpandedPoints
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTimerPointService

/-! Timer keepalives use the expanded native staging proof. The timer's
actual source and original preparation admission are preserved; the zero-arm
repayment and peer-release contracts retain their separately named scope. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.KeepaliveExpanded
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

def timerPoints (raw : Timer.Points.Zero.RawPoints) (release : WorkService.Points.ReleasePoints) :
    Timer.Points.ChildPoints := Timer.Points.children raw (Timer.Points.timerOther release RootPoint)

noncomputable def timer_contract {raw : Timer.Points.Zero.RawPoints}
    {nativeRelease insideRelease : WorkService.Points.ReleasePoints}
    {Good : List Event → World → Prop}
    (accept : ∀ledger pid (w : World) h (u : World) middle,
      Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (pid : PeerId) : Timer.Points.ChildSourceContract
      (timerPoints raw nativeRelease) (timerPoints raw insideRelease) Good (.keepalive pid) where
  remainder:=rootRemainder pid
  continuation:=fun _ _ _ _ point=>root_remainder_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    obtain ⟨ledger,account⟩:=before
    exact accept ledger pid w h u middle (point.evidence account)

/-- Timer keepalive cuts derive their packet accounting from the original
timer entry and preparation receipt, without a keepalive-source assumption. -/
noncomputable def timer_children {raw : Timer.Points.Zero.RawPoints}
    {nativeRelease insideRelease : WorkService.Points.ReleasePoints}
    {Good : List Event → World → Prop}
    (carrierGood : ∀h w,Timer.Points.Carrier h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (repayment : Timer.Points.Zero.ReleaseContract raw Good)
    (release : ∀peer,Timer.Points.ChildSourceContract
      (timerPoints raw nativeRelease) (timerPoints raw insideRelease) Good (.release peer))
    (accept : ∀ledger pid (w : World) h (u : World) middle,
      Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u) :
    Timer.Points.ChildContracts (timerPoints raw nativeRelease) (timerPoints raw insideRelease) Good :=
  Timer.Points.timer_contracts carrierGood pendingGood repayment release (timer_contract accept)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.KeepaliveExpanded
