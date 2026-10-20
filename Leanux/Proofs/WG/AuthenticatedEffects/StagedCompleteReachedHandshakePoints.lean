import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedHandshakeFrames

/-! All points are constructors of the fixed handshake source. Remainders are
built from that source and the concrete leaf/repayment proofs; an arbitrary
equal-run continuation cannot introduce a point. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.HandshakeConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

inductive Site where
  | entry | returned | release | keepalive | metadata
  | leaf (site : Consume.Leaf.Site)
  | left (site : Site) | right (site : Site)

inductive Point : {α : Type} → {action : PrefixM Event α} → Shape action →
    World → History → Site → World → History → Prop where
  | entry (shape : Shape action) : Point shape w h .entry w h
  | returned (shape : Shape action) (performed : runPrefix action w h=(.ok (value,u),middle)) :
      Point shape w h .returned u middle
  | metadata {w : World} {source : PeerMetadata.Shape body}
      (point : PeerMetadata.Point source w.wg w.ambient v b) :
      Point (.native (.metadata body source)) w h .metadata {w with wg:=v,ambient:=b} h
  | leaf (source : Consume.Leaf.Shape action)
      (point : Consume.Leaf.Point WorkService.Points.leafPoints source w h site u middle) :
      Point (.leaf source) w h (.leaf site) u middle
  | release (peer : Option PeerId) (point : PeerRetirement.Points.NativePoints peer w h u middle) :
      Point (.child (.release peer)) w h .release u middle
  | keepalive (pid : PeerId) (point : KeepaliveExpanded.RootPoint pid w h u middle) :
      Point (.child (.keepalive pid)) w h .keepalive u middle
  | left {body : PrefixM Event α} {next : α → PrefixM Event β} {head : Shape body}
      (tail : ∀value,Shape (next value)) (point : Point head w h site u middle) :
      Point (.bind head tail) w h (.left site) u middle
  | right {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀value,Shape (next value))
      (leading : runPrefix body w h=(.ok (value,u),middle))
      (point : Point (tail value) u middle site v last) :
      Point (.bind head tail) w h (.right site) v last

variable {Good : History → World → Prop}

theorem Point.safe (carrierGood : ∀h w,Carrier h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (before : Carrier h w) (point : Point shape w h site u middle) : Good middle u := by
  induction point with
  | entry shape=>
    exact carrierGood _ _ before
  | returned shape performed=>
    exact carrierGood _ _ (shape.normal before performed)
  | metadata point=>
    obtain ⟨ledger,account⟩:=before
    exact carrierGood _ _ ⟨ledger,account.same_view point.frame⟩
  | leaf source point=>
    exact carrierGood _ _
      (point.safe (fun _ _ h=>h) WorkService.Points.leafContracts before)
  | release peer point=>
      obtain ⟨ledger,accounted⟩:=before
      exact acceptPeer ledger _ _ (PeerRetirement.Points.native_evidence accounted point)
  | keepalive pid point=>
      obtain ⟨ledger,accounted⟩:=before
      exact acceptKeepalive ledger pid _ _ _ _ (point.evidence accounted)
  | left tail point ih=>
    exact ih before
  | right head tail leading point ih=>
    exact ih (head.normal before leading)

theorem Point.remaining {α : Type} {action : PrefixM Event α} {shape : Shape action}
    (point : Point shape w h site u middle) :
    ∃remaining : PrefixM Event α,runPrefix action w h=runPrefix remaining u middle := by
  induction point with
  | entry shape=>
    exact ⟨_,rfl⟩
  | returned shape performed=>
    exact ⟨pure _,performed⟩
  | metadata point=>exact point.observed_remaining _
  | leaf source point=>
      obtain ⟨remaining,residual⟩:=point.residual WorkService.Points.leafContracts
      exact ⟨remaining,residual.run⟩
  | release peer point=>
    exact ⟨_,PeerRetirement.Points.continuation_run point⟩
  | keepalive pid point=>exact point.residual
  | left tail point ih=>
      rename_i body next head
      obtain ⟨remaining,continued⟩:=ih
      exact ⟨remaining >>= next,Scheduler.bind_run_equal _ continued⟩
  | right head tail leading point ih=>
      obtain ⟨remaining,continued⟩:=ih
      exact ⟨remaining,by rw [runPrefix_bind,leading];exact continued⟩

def RootPoint (w : World) (h : History) (u : World) (middle : History) : Prop :=
  ∃site,Point source w h site u middle

noncomputable def remainder (point : RootPoint w h u middle) : PrefixM Event Bool :=
  Classical.choose (Classical.choose_spec point).remaining

theorem remainder_run (point : RootPoint w h u middle) :
    runPrefix (liftWGObserver (Driver.handshakeObserved hooks)) w h=runPrefix (remainder point) u middle :=
  Classical.choose_spec (Classical.choose_spec point).remaining

/-- The handshake worker retains packet conservation at every declared
source cut, including its actual callback scopes, receipts, expanded keepalive
and counted peer repayment. Finer native atom interiors remain explicit. -/
theorem root_safe (carrierGood : ∀h w,Carrier h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (before : Carrier h w) (point : RootPoint w h u middle) : Good middle u := by
  obtain ⟨site,point⟩:=point
  exact point.safe carrierGood acceptPeer acceptKeepalive before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.HandshakeConcrete
