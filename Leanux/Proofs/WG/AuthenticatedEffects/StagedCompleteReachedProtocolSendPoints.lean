import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProtocolSendFrames

/-! All points are constructors of the fixed sender source. Remainders are
built from that source and the concrete leaf/repayment proofs; an arbitrary
equal-run continuation cannot introduce a point. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProtocolSend
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

inductive Site where
  | entry | returned | release | creation | mac | socket
  | leaf (site : Consume.Leaf.Site)
  | left (site : Site) | right (site : Site)

inductive Point : {α : Type} → {action : PrefixM Event α} → Shape action →
    World → History → Site → World → History → Prop where
  | entry (shape : Shape action) : Point shape w h .entry w h
  | returned (shape : Shape action) (performed : runPrefix action w h=(.ok (value,u),middle)) :
      Point shape w h .returned u middle
  | creation {w : World} (point : PeerMetadata.Point (PeerMetadata.initiationShape pid) w.wg w.ambient v b) :
      Point (.native (.create pid)) w h .creation {w with wg:=v,ambient:=b} h
  | mac {w : World} (point : PeerMetadata.Point (PeerMetadata.addMacShape pid bytes) w.wg w.ambient v b) :
      Point (.native (.mac pid bytes)) w h .mac {w with wg:=v,ambient:=b} h
  | socket (point : ProtocolPoints.RootPoint pid bytes w h u middle) :
      Point (.native (.socket pid bytes)) w h .socket u middle
  | leaf (source : Consume.Leaf.Shape action)
      (point : Consume.Leaf.Point WorkService.Points.leafPoints source w h site u middle) :
      Point (.leaf source) w h (.leaf site) u middle
  | release (peer : Option PeerId) (point : PeerRetirement.Points.NativePoints peer w h u middle) :
      Point (.release peer) w h .release u middle
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
    (before : Carrier h w) (point : Point shape w h site u middle) : Good middle u := by
  induction point with
  | entry shape=>
    exact carrierGood _ _ before
  | returned shape performed=>
    exact carrierGood _ _ (shape.normal before performed)
  | creation point=>
    obtain ⟨ledger,account⟩:=before
    exact carrierGood _ _ ⟨ledger,account.same_view point.frame⟩
  | mac point=>
    obtain ⟨ledger,account⟩:=before
    exact carrierGood _ _ ⟨ledger,account.same_view point.frame⟩
  | socket point=>exact carrierGood _ _ (ProtocolPoints.Point.accounted before point)
  | leaf source point=>
    exact carrierGood _ _
      (point.safe (fun _ _ h=>h) WorkService.Points.leafContracts before)
  | release peer point=>
      obtain ⟨ledger,accounted⟩:=before
      exact acceptPeer ledger _ _ (PeerRetirement.Points.native_evidence accounted point)
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
  | creation point=>exact point.observed_remaining _
  | mac point=>exact point.observed_remaining _
  | socket point=>exact ProtocolPoints.Point.remaining point
  | leaf source point=>
      obtain ⟨remaining,residual⟩:=point.residual WorkService.Points.leafContracts
      exact ⟨remaining,residual.run⟩
  | release peer point=>
    exact ⟨_,PeerRetirement.Points.continuation_run point⟩
  | left tail point ih=>
      rename_i body next head
      obtain ⟨remaining,continued⟩:=ih
      exact ⟨remaining >>= next,Scheduler.bind_run_equal _ continued⟩
  | right head tail leading point ih=>
      obtain ⟨remaining,continued⟩:=ih
      exact ⟨remaining,by rw [runPrefix_bind,leading];exact continued⟩

def RootPoint (pid : PeerId) (w : World) (h : History) (u : World) (middle : History) : Prop :=
  ∃site,Point (source pid) w h site u middle

noncomputable def remainder (point : RootPoint pid w h u middle) : PrefixM Event Unit :=
  Classical.choose (Classical.choose_spec point).remaining

theorem remainder_run (point : RootPoint pid w h u middle) :
    runPrefix (liftWGObserver (CausalJournal.flushedSend pid)) w h=runPrefix (remainder point) u middle :=
  Classical.choose_spec (Classical.choose_spec point).remaining

/-- A flushed protocol sender retains packet conservation through its fixed
source, timer helpers and counted peer repayment. Each declared cut has its
original continuation, including before a later stopped suffix. -/
theorem root_safe (carrierGood : ∀h w,Carrier h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (before : Carrier h w) (point : RootPoint pid w h u middle) : Good middle u := by
  obtain ⟨site,point⟩:=point
  exact point.safe carrierGood acceptPeer before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProtocolSend
