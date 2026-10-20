import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSkbAccessFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePollNative

/-! RX erasure keeps the TX ledger and transports packet bounds through the
actual adapter write-back; it does not claim equality of the full snapshot. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NapiMetadata
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal

theorem free_account (point : SkbAccess.Point (SkbStore.freeRx skb) w a v b)
    (before : CompleteCarrier.Accounted h ledger debts locals w) :
    CompleteCarrier.Accounted h ledger debts locals v := by
  cases point with
  | read point => exact before.same_view point.frame
  | component device performed => exact before
  | returned performed =>
      exact ⟨(hoare_iff_run_ambient _ _ _).mp (CompletePollNative.free_rx_entry skb)
        _ _ _ _ _ before.1 performed,before.2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NapiMetadata
