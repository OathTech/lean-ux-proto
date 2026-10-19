import Leanux.Proofs.WG.TransmitSecurity.StagedCompletionNativeFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedFocusedProduct
import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityCompletionAppendFrames
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeCausalProjection

/-! The actual completion, terminal disposal and nested repayments retain
staged origins. Append-only history, projection frames and native state
preservation are proved independently. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged
open AuthenticatedEffects AuthenticatedEffects.CausalJournal

theorem transmit (pid : PeerId) : ProductSafe (CausalJournal.transmit pid) := by
  apply product_quiet (CallbackQuiet.transmit_appends pid)
    (HandshakeSecurity.ExchangeCausal.transmit_history_of_quiet selection?
      (fun event => by cases event <;> rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) pid)
  · exact CallbackFrames.product_erases _ (HandshakeSecurity.ExchangeCausal.transmit_projects pid)
      (erasesPrefix_lift _)
  · intro history
    exact Native.product _ (Native.transmit pid)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
