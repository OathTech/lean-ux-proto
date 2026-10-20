import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPrefixStoreSource

/-! Fixed native runner-helper points retain the packet ledger and the
allocation companion of their own successful leading source prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PrefixStore
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

theorem Shape.checked (source : Shape action) : CompleteProduct.Checked action := by
  induction source with
  | pure value => exact CompleteProduct.pure_checked value
  | native source => exact source.checked
  | bind head tail ihHead ihTail => exact CompleteProduct.bind_checked ihHead ihTail

theorem Shape.normal (source : Shape action) (before : CompleteProduct.Carrier h w)
    (performed : runPrefix action w h=(.ok (value,v),last)) : CompleteProduct.Carrier last v := by
  obtain ⟨_,_,_,post⟩ := source.checked w h before
  simpa only [performed] using post

theorem Point.carrier (point : Point source w h v last) (before : CompleteProduct.Carrier h w) :
    CompleteProduct.Carrier last v := by
  induction point with
  | entry source => exact before
  | returned source performed => exact source.normal before performed
  | native point => exact point.carrier before
  | left tail point ih => exact ih before
  | right head tail leading point ih => exact ih (head.normal before leading)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PrefixStore
