import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRoutedTransmitSource

/-! Concrete accounts at the original routed caller's phase boundaries.
Expanded callback evidence preserves pending receipts instead of treating
them as completed ownership transfers. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
abbrev Account := Lifecycle.Points.Account

theorem front_normal (before : Account h w)
    (performed : runPrefix (front input) w h=(.ok (result,u),middle)) : Account middle u := by
  have checked:=CompletePoll.state CompleteProduct.Safe
    (CompleteFront.checked input CompleteProduct.Safe CompleteProduct.account_safe)
  obtain ⟨_,_,_,kept⟩:=checked w h before
  unfold front at performed
  rw [performed] at kept
  exact kept

theorem stage_normal (before : Account h w)
    (performed : runPrefix (stage pid) w h=(.ok ((),u),middle)) : Account middle u := by
  have checked:=CompletePoll.state (CompleteTransmit.Safe []) (CompleteTransmit.staging (locals:=[]) pid)
  obtain ⟨_,_,_,kept⟩:=checked w h before
  unfold stage at performed
  rw [performed] at kept
  exact kept

theorem normal (before : Account h w)
    (performed : runPrefix (action input) w h=(.ok (value,u),middle)) : Account middle u := by
  have checked:=CompletePoll.state (CompleteTransmit.Safe [])
    (CompleteTransmit.transmit (locals:=[]) input.family input.address input.packets input.mtu)
  obtain ⟨_,_,_,kept⟩:=checked w h before
  unfold action at performed
  rw [performed] at kept
  exact kept

variable {Good : History → World → Prop}

/-- Every declared routed-transmit cut retains its packet account or the
actual staging/release pending-receipt evidence, derived from the original
entry. Internal front admission/receipt intervals remain a separate boundary. -/
theorem Point.safe
    (accountGood : ∀h w,Account h w → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (before : Account h w) (point : Point input w h u middle) : Good middle u := by
  cases point with
  | entry=>exact accountGood _ _ before
  | frontReturned performed=>exact accountGood _ _ (front_normal before performed)
  | staging admitted point=>
    obtain ⟨ledger,account⟩:=front_normal before admitted
    exact acceptStaging ledger _ _ (point.evidence account)
  | repayment admitted staged point=>
    obtain ⟨ledger,account⟩:=stage_normal (front_normal before admitted) staged
    exact acceptPeer ledger _ _ (PeerRetirement.Points.native_evidence account point)
  | returned performed=>exact accountGood _ _ (normal before performed)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
