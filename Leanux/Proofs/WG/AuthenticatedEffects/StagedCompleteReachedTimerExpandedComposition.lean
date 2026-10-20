import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedKeepaliveExpandedTimer
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTimerZeroRawContract
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerPointLifted

/-! The timer family supplies its raw zero-key repayment, observed peer
release and expanded keepalive children. Evidence acceptance remains explicit;
there is no assumed deeper timer-child continuation or safety contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Composition
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev History := List Event
variable {Good : History → World → Prop}

def points : Points.ChildPoints :=
  KeepaliveExpanded.timerPoints Points.Zero.rawPoints PeerRetirement.Points.NativePoints

noncomputable def release (accept : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (peer : Option PeerId) : Points.ChildSourceContract points points Good (.release peer) where
  remainder:=fun _ _ _ _ point=>PeerRetirement.Points.continuation point
  continuation:=fun _ _ _ _ point=>PeerRetirement.Points.continuation_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    obtain ⟨ledger,account⟩:=before
    exact accept ledger middle u (PeerRetirement.Points.native_evidence account point)

/-- The declared timer children conserve their original packet lineage,
including purge's pending receipt, the funded raw repayment and keepalive
admission, with source-derived remainders for all three child families. -/
noncomputable def children
    (carrierGood : ∀h w,Points.Carrier h w → Good h w)
    (pendingGood : ∀h w,Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u) :
    Points.ChildContracts points points Good :=
  KeepaliveExpanded.timer_children carrierGood pendingGood (Points.Zero.raw_contract carrierGood)
    (release acceptPeer) acceptKeepalive

/-- Every declared canonical timer point has packet-conservation evidence
and the exact remaining source, including stopped paths. Its entry account
is explicit; initialized caller composition remains a separate obligation. -/
theorem root_safe
    (carrierGood : ∀h w,Points.Carrier h w → Good h w)
    (pendingGood : ∀h w,Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (before : Points.Carrier h w) (point : Points.RootPoint points root w h u middle) :
    Good middle u ∧ ∃remaining,runPrefix root.action w h=runPrefix remaining u middle := by
  obtain ⟨site,point⟩:=point
  let contracts:=children carrierGood pendingGood acceptPeer acceptKeepalive
  refine ⟨point.safe carrierGood contracts before,?_⟩
  obtain ⟨rest,residual⟩:=point.residual contracts
  exact ⟨rest,residual.run⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Timer.Composition
