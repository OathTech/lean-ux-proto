import Leanux.Proofs.WG.AuthenticatedEffects.CausalSelectionHistory
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptQuietHistory
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNestedFrames
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNativeCallbacks
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietNative

/-! Real enriched callback receipts preserve prior work/timer selection
checks. The selector retains precisely the constructors whose checks matter. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

def protected? : Event → Option Unit
  | .old (.timerSelected _) => some ()
  | .scope (.entered ⟨_,.sendWork _ _⟩) => some ()
  | .scope (.entered ⟨_,.timer _ _ _ _⟩) => some ()
  | _ => none

theorem quiet_of_absent (event : Event) (quiet : protected? event = none) : Quiet event := by
  cases event with
  | old event => cases event <;> first | trivial | cases quiet
  | scope scope =>
    cases scope with
    | entered token => cases token with | mk index cause => cases cause <;> first | trivial | cases quiet
    | exited _ => trivial
  | _ => trivial

theorem callback_state (quiet : CallbackQuiet.StateQuiet protected? body) : Driver.StateHistorySafe Safe body :=
  CallbackQuiet.state_safe quiet (fun _ _ safe silent =>
    safe.quiet (fun event member => quiet_of_absent event (silent event member)))

theorem callback_product (quiet : CallbackQuiet.ProductQuiet protected? body) : Driver.ProductHistorySafe Safe body :=
  CallbackQuiet.product_safe quiet (fun _ _ safe silent =>
    safe.quiet (fun event member => quiet_of_absent event (silent event member)))

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
