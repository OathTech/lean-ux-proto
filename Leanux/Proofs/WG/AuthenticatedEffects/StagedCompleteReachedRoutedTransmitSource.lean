import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDumpConcreteRunner
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedFrontCutsSource

/-! Routed transmit's literal front, staging and repayment order. Fixed front
points include overflow mutations and pending birth receipts. Other front
native atoms remain explicit; all children retain their original source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev Input := Transmit.Input
abbrev History := List Event

def action (input : Input) : PrefixM Event Int :=
  liftWGObserver (Driver.transmitObserved hooks input.family input.address input.packets input.mtu)

def front (input : Input) : PrefixM Event (Except Int PeerId) :=
  liftWGObserver (CausalJournal.front input.family input.address input.packets input.mtu)

def stage (pid : PeerId) : PrefixM Event Unit := liftWGObserver (Driver.stagingObserved hooks pid)
def release (pid : PeerId) : PrefixM Event Unit := liftWGObserver (hooks.peerRelease (some pid))
def repayment (pid : PeerId) : PrefixM Event Int := release pid >>= fun _=>pure 0

def tail : Except Int PeerId → PrefixM Event Int
  | .error err=>pure err
  | .ok pid=>stage pid >>= fun _=>repayment pid

theorem source (input : Input) : action input=(front input >>= tail) := by
  unfold action
  rw [Transmit.factor,liftWGObserver_bind]
  congr 1
  funext result
  cases result with
  | error err=>rfl
  | ok pid=>simp only [Transmit.tail,Transmit.repayment,liftWGObserver_bind];rfl

theorem after_front (performed : runPrefix (front input) w h=(.ok (result,u),middle)) :
    runPrefix (action input) w h=runPrefix (tail result) u middle := by
  rw [source,runPrefix_bind,performed]

theorem after_stage (admitted : runPrefix (front input) w h=(.ok (.ok pid,q),prior))
    (staged : runPrefix (stage pid) q prior=(.ok ((),u),middle)) :
    runPrefix (action input) w h=runPrefix (repayment pid) u middle := by
  rw [after_front admitted,tail,runPrefix_bind,staged]

inductive Point (input : Input) (w : World) (h : History) : World → History → Prop where
  | entry : Point input w h w h
  | frontCut (point : FrontCuts.RootPoint input w h u middle) : Point input w h u middle
  | frontReturned (performed : runPrefix (front input) w h=(.ok (result,u),middle)) :
      Point input w h u middle
  | staging (admitted : runPrefix (front input) w h=(.ok (.ok pid,q),prior))
      (point : StagingExpanded.RootPoint pid q prior u middle) : Point input w h u middle
  | repayment (admitted : runPrefix (front input) w h=(.ok (.ok pid,q),prior))
      (staged : runPrefix (stage pid) q prior=(.ok ((),v),events))
      (point : PeerRetirement.Points.NativePoints (some pid) v events u middle) :
      Point input w h u middle
  | returned (performed : runPrefix (action input) w h=(.ok (value,u),middle)) :
      Point input w h u middle

theorem Point.remaining (point : Point input w h u middle) :
    ∃remaining,runPrefix (action input) w h=runPrefix remaining u middle := by
  cases point with
  | entry=>exact ⟨_,rfl⟩
  | frontCut point=>
      obtain ⟨remaining,continued⟩:=point.remaining
      exact ⟨remaining >>= tail,(congrArg (fun action=>runPrefix action w h) (source input)).trans
        (Scheduler.bind_run_equal tail continued)⟩
  | frontReturned performed=>exact ⟨_,after_front performed⟩
  | staging admitted point=>
    obtain ⟨remaining,continued⟩:=point.residual
    exact ⟨remaining >>= fun _=>RoutedTransmit.repayment _,(after_front admitted).trans
      (Scheduler.bind_run_equal _ continued)⟩
  | repayment admitted staged point=>
    exact ⟨PeerRetirement.Points.continuation point >>= fun _=>pure 0,
      (after_stage admitted staged).trans
        (Scheduler.bind_run_equal _ (PeerRetirement.Points.continuation_run point))⟩
  | returned performed=>exact ⟨pure _,performed⟩

noncomputable def remainder (point : Point input w h u middle) : PrefixM Event Int :=
  Classical.choose point.remaining

theorem remainder_run (point : Point input w h u middle) :
    runPrefix (action input) w h=runPrefix (remainder point) u middle :=
  Classical.choose_spec point.remaining

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
