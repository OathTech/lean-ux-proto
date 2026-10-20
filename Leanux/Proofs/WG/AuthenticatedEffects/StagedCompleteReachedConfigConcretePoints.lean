import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigChildrenFrames

/-! Configuration points are fixed-source constructors. Actual successful
prefixes supply bind continuations and the saved-peer write's intermediate cuts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing TransmitSecurity CausalJournal

inductive Site where
  | entry | returned | child | saved | pskRead | metadata | lookup | creation
  | left (site : Site) | right (site : Site)

inductive Point : {α : Type} → {action : PrefixM Event α} → Shape action →
    World → History → Site → World → History → Prop where
  | entry (source : Shape action) : Point source w h .entry w h
  | returned (source : Shape action) (performed : runPrefix action w h=(.ok (value,u),middle)) :
      Point source w h .returned u middle
  | creation {w : World} (point : PeerCreation.Point key psk w.wg w.ambient v b) :
      Point (.native (.create key psk)) w h .creation {w with wg:=v,ambient:=b} h
  | metadata {w : World} (allocated : Preserves RetirementSecurity.StackOwnership.Allocated action)
      (point : PeerMetadata.Point source w.wg w.ambient v b) :
      Point (.native (.metadata action source allocated)) w h .metadata {w with wg:=v,ambient:=b} h
  | lookup {w : World} (allocated : Preserves RetirementSecurity.StackOwnership.Allocated action)
      (point : Lookup.Point source w.wg w.ambient v b) :
      Point (.native (.lookup action source allocated)) w h .lookup {w with wg:=v,ambient:=b} h
  | child (family : Family) (point : family.Point w h u middle) : Point (.child family) w h .child u middle
  | saved (point : ConfigSaved.Point pid running interval w h u middle) :
      Point (.saved pid running interval) w h .saved u middle
  | pskRead (performed : runPrefix (ConfigSaved.read pid) w h=(.ok (p,u),middle)) :
      Point (.psk pid psk) w h .pskRead u middle
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
  | creation point=>exact point.observed_remaining _
  | metadata allocated point=>exact point.observed_remaining _
  | lookup allocated point=>exact point.observed_remaining _
  | child family point=>exact point.remaining
  | saved point=>exact point.remaining
  | pskRead performed=>exact ⟨_,by rw [psk_source,runPrefix_bind,performed]⟩
  | left tail point ih=>
      obtain ⟨remaining,continued⟩:=ih
      exact ⟨remaining >>= _,Scheduler.bind_run_equal _ continued⟩
  | right head tail leading point ih=>
      obtain ⟨remaining,continued⟩:=ih
      exact ⟨remaining,by rw [runPrefix_bind,leading];exact continued⟩

variable {Good : History → World → Prop}

/-- Security: configuration source cuts conserve the initialized packet
account through allocation, saved metadata writes, removal and fixture sends.
The fixed native atoms remain explicit finer-coverage boundaries. -/
theorem Point.safe
    (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (before : CompleteProduct.Carrier h w) (point : Point source w h site u middle) : Good middle u := by
  induction point with
  | entry source=>exact accountGood _ _ before.1
  | returned source performed=>exact accountGood _ _ (source.normal before performed).1
  | creation point=>
      obtain ⟨ledger,account⟩:=before.1
      exact accountGood _ _ ⟨ledger,point.accounted account before.2.choose_spec.peerSlots⟩
  | metadata allocated point=>
      obtain ⟨ledger,account⟩:=before.1
      exact accountGood _ _ ⟨ledger,account.same_view point.frame⟩
  | lookup allocated point=>
      obtain ⟨ledger,account⟩:=before.1
      exact accountGood _ _ ⟨ledger,account.same_view point.frame⟩
  | child family point=>exact point.safe accountGood pendingGood acceptPeer acceptStaging acceptKeepalive before
  | saved point=>exact accountGood _ _ (point.normal before).1
  | pskRead performed=>exact accountGood _ _ (Xmit.normal (ConfigSaved.read_checked _) before performed).1
  | left tail point ih=>exact ih before
  | right head tail leading point ih=>exact ih (head.normal before leading)

def RootPoint (attrs : DeviceAttrs) (w : World) (h : History) (u : World) (middle : History) : Prop :=
  ∃site,Point (deviceShape attrs) w h site u middle

noncomputable def remainder (point : RootPoint attrs w h u middle) : PrefixM Event Int :=
  Classical.choose (Classical.choose_spec point).remaining

theorem remainder_run (point : RootPoint attrs w h u middle) :
    runPrefix (liftWGObserver (Driver.configDevice hooks attrs)) w h=runPrefix (remainder point) u middle :=
  Classical.choose_spec (Classical.choose_spec point).remaining

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
