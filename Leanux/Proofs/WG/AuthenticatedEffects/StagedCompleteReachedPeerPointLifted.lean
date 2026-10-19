import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerPointCoverage

/-! Peer release changes only its WG projection and ambient input. The
fixed native points lift to the actual outer world without an unrelated
existential snapshot or an arbitrary continuation equation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Points
open Leanux Leanux.WG Leanux.Proofs.Logged CausalJournal CompleteCarrier

inductive LiftedPoint (peer : Option PeerId) (w : World) (h : History) :
    World → History → Type 1 where
  | lifted (point : Point peer w.wg w.ambient h u b middle) :
      LiftedPoint peer w h {w with wg:=u,ambient:=b} middle

def LiftedPoint.remainder (point : LiftedPoint peer w h u middle) : PrefixM Event Unit :=
  match point with
  | .lifted point => liftWGObserver point.remainder

theorem LiftedPoint.continuation (point : LiftedPoint peer w h u middle) :
    runPrefix (liftWGObserver (CausalJournal.peerRelease peer)) w h=
      runPrefix point.remainder u middle := by
  cases point with
  | lifted point =>
    change runPrefix (liftWGObserver (CausalJournal.peerRelease peer)) w h=
      runPrefix (liftWGObserver point.remainder) _ _
    rw [liftWGObserver_run,liftWGObserver_run,point.continuation]

theorem LiftedPoint.evidence (before : Accounted h ledger debts locals w.wg)
    (point : LiftedPoint peer w h u middle) : Evidence ledger debts locals middle u.wg := by
  cases point with
  | lifted point => exact point.evidence before

abbrev NativePoints (peer : Option PeerId) (w : World) (h : History) (u : World) (middle : History) : Prop :=
  Nonempty (LiftedPoint peer w h u middle)

noncomputable def continuation (point : NativePoints peer w h u middle) : PrefixM Event Unit :=
  (Classical.choice point).remainder

theorem continuation_run (point : NativePoints peer w h u middle) :
    runPrefix (liftWGObserver (CausalJournal.peerRelease peer)) w h=
      runPrefix (continuation point) u middle :=
  (Classical.choice point).continuation

theorem native_evidence (before : Accounted h ledger debts locals w.wg)
    (point : NativePoints peer w h u middle) : Evidence ledger debts locals middle u.wg :=
  (Classical.choice point).evidence before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Points
