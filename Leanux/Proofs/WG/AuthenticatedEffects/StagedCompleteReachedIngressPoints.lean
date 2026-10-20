import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIngressFrames

/-! UDP ingress points use the fixed receive source and actual successful
prefixes. Counted release interiors retain their original continuation;
RX storage changes transport the same complete TX account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Ingress
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing TransmitSecurity CausalJournal RetirementSecurity

inductive Site where
  | entry | returned | release | access | lookup | rxQueue | allocate | free
  | left (site : Site) | right (site : Site)

inductive Point : {α : Type} → {action : PrefixM Event α} → Shape action →
    World → History → Site → World → History → Prop where
  | entry (source : Shape action) : Point source w h .entry w h
  | returned (source : Shape action) (performed : runPrefix action w h=(.ok (value,u),middle)) :
      Point source w h .returned u middle
  | access {α : Type} {action : WG.M α} {source : Access.Shape action} {w : World}
      (allocated : Preserves StackOwnership.Allocated action)
      (point : Access.Point source w.wg w.ambient v b) :
      Point (.native (.access action source allocated)) w h .access {w with wg:=v,ambient:=b} h
  | lookup {w : World} (point : Lookup.Point (Lookup.canonical kinds number) w.wg w.ambient v b) :
      Point (.native (.lookup kinds number)) w h .lookup {w with wg:=v,ambient:=b} h
  | rxQueue {w : World} (point : RxQueueAccess.Point skb w.wg w.ambient v b) :
      Point (.native (.rxQueue skb)) w h .rxQueue {w with wg:=v,ambient:=b} h
  | allocate {w : World} (point : SkbAccess.Point (SkbStore.newRx packet) w.wg w.ambient v b) :
      Point (.native (.allocate packet)) w h .allocate {w with wg:=v,ambient:=b} h
  | free {w : World} (point : SkbAccess.Point (SkbStore.freeRx skb) w.wg w.ambient v b) :
      Point (.native (.free skb)) w h .free {w with wg:=v,ambient:=b} h
  | release (point : PeerRetirement.Points.NativePoints peer w h u middle) :
      Point (.release peer) w h .release u middle
  | left {body : PrefixM Event α} {next : α → PrefixM Event β} {head : Shape body}
      (tail : ∀value,Shape (next value)) (point : Point head w h site u middle) :
      Point (.bind head tail) w h (.left site) u middle
  | right {body : PrefixM Event α} {next : α → PrefixM Event β}
      (head : Shape body) (tail : ∀value,Shape (next value))
      (leading : runPrefix body w h=(.ok (value,u),middle))
      (point : Point (tail value) u middle site v last) : Point (.bind head tail) w h (.right site) v last

theorem Point.remaining {α : Type} {action : PrefixM Event α} {source : Shape action}
    (point : Point source w h site u middle) :
    ∃remaining,runPrefix action w h=runPrefix remaining u middle := by
  induction point with
  | entry source=>exact ⟨_,rfl⟩
  | returned source performed=>exact ⟨pure _,performed⟩
  | access allocated point=>exact point.observed_remaining _
  | lookup point=>exact point.observed_remaining _
  | rxQueue point=>exact point.observed_remaining _
  | allocate point=>exact point.observed_remaining _
  | free point=>exact point.observed_remaining _
  | release point=>exact ⟨PeerRetirement.Points.continuation point,PeerRetirement.Points.continuation_run point⟩
  | left tail point ih=>
      obtain ⟨remaining,continued⟩:=ih
      exact ⟨remaining >>= _,Scheduler.bind_run_equal _ continued⟩
  | right head tail leading point ih=>
      obtain ⟨remaining,continued⟩:=ih
      exact ⟨remaining,by rw [runPrefix_bind,leading];exact continued⟩

variable {Good : History → World → Prop}

/-- Security: UDP ingress preserves the complete TX packet ledger through
its actual RX allocation, admission, refusal cleanup and counted peer release.
RX cells do not introduce independently born TX obligations. -/
theorem Point.safe (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (before : CompleteProduct.Carrier h w) (point : Point source w h site u middle) : Good middle u := by
  induction point with
  | entry source=>exact accountGood _ _ before.1
  | returned source performed=>exact accountGood _ _ (source.normal before performed).1
  | access allocated point=>
      obtain ⟨ledger,account⟩:=before.1
      exact accountGood _ _ ⟨ledger,account.entry.same_view point.frame,account.complete⟩
  | lookup point=>
      obtain ⟨ledger,account⟩:=before.1
      exact accountGood _ _ ⟨ledger,account.entry.same_view point.frame,account.complete⟩
  | rxQueue point=>
      obtain ⟨ledger,account⟩:=before.1
      exact accountGood _ _ ⟨ledger,account.entry.same_view point.frame,account.complete⟩
  | allocate point=>
      rcases point.same_or_returned with same|⟨value,performed⟩
      · obtain ⟨ledger,account⟩:=before.1
        exact accountGood _ _ ⟨ledger,account.entry.same_view same,account.complete⟩
      · obtain ⟨ledger,account⟩:=before.1
        exact accountGood _ _ ⟨ledger,
          (hoare_iff_run_ambient _ _ _).mp (CompleteIngress.new_rx_entry _) _ _ value _ _ account.entry performed,
          account.complete⟩
  | free point=>
      rcases point.same_or_returned with same|⟨value,performed⟩
      · obtain ⟨ledger,account⟩:=before.1
        exact accountGood _ _ ⟨ledger,account.entry.same_view same,account.complete⟩
      · obtain ⟨ledger,account⟩:=before.1
        exact accountGood _ _ ⟨ledger,
          (hoare_iff_run_ambient _ _ _).mp (CompletePollNative.free_rx_entry _) _ _ value _ _ account.entry performed,
          account.complete⟩
  | release point=>
      obtain ⟨ledger,account⟩:=before.1
      exact acceptPeer ledger _ _ (PeerRetirement.Points.native_evidence account point)
  | left tail point ih=>exact ih before
  | right head tail leading point ih=>exact ih (head.normal before leading)

def RootPoint (msg : List UInt8) (src : SkbSource) (w : World) (h : History) (u : World) (middle : History) : Prop :=
  ∃site,Point (canonical msg src) w h site u middle

theorem RootPoint.remaining (point : RootPoint msg src w h u middle) :
    ∃remaining,runPrefix (Driver.receiveEntryObserved hooks msg src) w h=runPrefix remaining u middle :=
  (Classical.choose_spec point).remaining

theorem RootPoint.safe (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (before : CompleteProduct.Carrier h w) (point : RootPoint msg src w h u middle) : Good middle u :=
  (Classical.choose_spec point).safe accountGood acceptPeer before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Ingress
