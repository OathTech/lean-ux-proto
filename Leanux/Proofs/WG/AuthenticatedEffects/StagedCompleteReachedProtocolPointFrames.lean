import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProtocolPointSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedProtocolFrames

/-! Protocol-send interiors preserve the same TX account at each actual point, including before the original socket receipt and later byte accounting. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProtocolPoints
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal

theorem Point.accounted (before : Carrier h w) (point : Point source w h u middle) : Carrier middle u := by
  induction point with
  | entry source=>exact before
  | returned source performed=>exact source.normal before performed
  | native point=>obtain ⟨ledger,account⟩:=before;exact ⟨ledger,account.same_view point.frame⟩
  | socket point=>obtain ⟨ledger,account⟩:=before;exact ⟨ledger,account.same_view point.frame⟩
  | left tail point ih=>exact ih before
  | right head tail leading point ih=>exact ih (head.normal before leading)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ProtocolPoints
