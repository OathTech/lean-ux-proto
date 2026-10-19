import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixReceiveTail
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryKeyObserved

/-! Endpoint selection and the actual confirmation receipt precede receive
maintenance in the same execution. Only the real staging callback remains
an input contract, and every receipt is independently terminal-quiet. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ReceiveConsumer
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal _root_.Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Passive
open CompleteCarrier (Accounted)
variable {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}
variable (Safe : List Event → Prop)
variable (accountSafe : ∀ ledger h w, Accounted h ledger debts locals w → Safe h)
include accountSafe

theorem confirmation (pid : PeerId) (kid : KeypairId) : Checked debts locals Safe
    (CausalJournal.state (Journal.confirmation pid kid)) := by
  unfold state Journal.confirmation HandshakeSecurity.Responder.DriverCuts.confirmation
  rw [Staged.Origins.focused_native_receipt,Staged.Origins.focused_native_receipt]
  exact receipt Safe accountSafe _ _ (Passive.native Safe accountSafe _ (KeyFrames.confirm pid kid))
    (fun _ => rfl) (fun _ _ => rfl)

/-- Actual receive consumption retains the paired ticket ledger through
endpoint, confirmation, staging and the complete receive/release suffix. -/
theorem checked (pid : PeerId) (packet : RxPacket) (endpoint : Endpoint)
    (staging : Checked debts locals Safe (Driver.stagingObserved CausalJournal.hooks pid)) :
    Checked debts locals Safe (Driver.consumeObserved CausalJournal.hooks pid packet endpoint) := by
  unfold Driver.consumeObserved
  exact bind_checked Safe (ReceiveFinish.endpoint Safe accountSafe pid endpoint) (fun _ =>
    bind_checked Safe (confirmation Safe accountSafe pid packet.keypair) (fun confirmed =>
      ReceiveTail.checked Safe accountSafe pid packet confirmed staging))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.ReceiveConsumer
