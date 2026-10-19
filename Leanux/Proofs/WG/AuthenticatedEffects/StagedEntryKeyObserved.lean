import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryKeyFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryPassive
import Leanux.Proofs.WG.TransmitSecurity.StagedHandshakeAdapters

/-! Session and confirmation observers retain the complete ticket ledger.
Their actual captured native operations edit key/handshake fields only. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.KeyObserved
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity TransmitSecurity.Staged.Obligations
open TransmitSecurity.Staged.Origins CausalJournal Passive
variable {ledger : Ledger} {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}

theorem receipt_checked (body : WGPrefix Event α) (record : WGRunWitness α → Event)
    (checked : Checked ledger debts locals body) (quiet : ∀ r, birthPackets (record r) = []) :
    Checked ledger debts locals (receiptWGObserved body record) := by
  unfold receiptWGObserved
  apply bind_checked (StatePrefixPreserves.captureWGObserved checked)
  intro r
  exact bind_checked (emit (record r) (quiet r)) (fun _ => pure_checked r.value)

theorem session (pid : PeerId) : Checked ledger debts locals (CausalJournal.session pid) := by
  unfold CausalJournal.session HandshakeSecurity.ExchangeJoint.session
  apply receipt_checked
  · unfold state Journal.session HandshakeSecurity.Responder.DriverCuts.session
    rw [Staged.Origins.focused_native_receipt,Staged.Origins.focused_native_receipt]
    exact receipt _ (KeyFrames.session pid) _ (fun _ => rfl)
  · intro r; rfl

theorem confirmation (pid : PeerId) (kid : KeypairId) :
    Checked ledger debts locals (state (Journal.confirmation pid kid)) := by
  unfold state Journal.confirmation HandshakeSecurity.Responder.DriverCuts.confirmation
  rw [Staged.Origins.focused_native_receipt,Staged.Origins.focused_native_receipt]
  exact receipt _ (KeyFrames.confirm pid kid) _ (fun _ => rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.KeyObserved
