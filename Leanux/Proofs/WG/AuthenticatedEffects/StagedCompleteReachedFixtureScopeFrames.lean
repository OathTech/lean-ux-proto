import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedFixtureScopeSource

/-! Fixture scope markers preserve both the current packet ledger and C1's
allocation companion. Interior safety is obtained from the original body at
the actual entered history, not from a new caller account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.FixtureScope
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal

theorem entered_carrier (before : CompleteProduct.Carrier h w) :
    CompleteProduct.Carrier (entered trigger h) w := by
  obtain ⟨⟨ledger,account⟩,allocated⟩:=before
  exact ⟨⟨ledger,account.append_quiet [_]
    (by intro event member; simp only [List.mem_singleton] at member; subst event; rfl)
    (by intro event member; simp only [List.mem_singleton] at member; subst event; exact fun _=>rfl)⟩,allocated⟩

variable {body : WGPrefix Event Unit} {inside : BodyPoints}

theorem Point.safe {Good : History → World → Prop}
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (checked : CompleteProduct.Checked (liftWGObserver body))
    (bodySafe : ∀w h u middle,CompleteProduct.Carrier h w → inside w h u middle → Good middle u)
    (before : CompleteProduct.Carrier h w) (point : Point trigger body inside w h u middle) : Good middle u := by
  cases point with
  | entry=>exact carrierGood _ _ before
  | entered=>exact carrierGood _ _ (entered_carrier before)
  | interior point=>exact bodySafe _ _ _ _ (entered_carrier before) point
  | exit performed=>
    obtain ⟨_,_,_,post⟩:=checked w (FixtureScope.entered trigger h) (entered_carrier before)
    rw [performed] at post
    exact carrierGood _ _ post
  | returned performed=>
    rw [source] at performed
    obtain ⟨_,_,_,post⟩:=CompleteProduct.scope (.fixture trigger) _ (fun _=>checked) w h before
    rw [performed] at post
    exact carrierGood _ _ post

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.FixtureScope
