import Leanux.Proofs.WG.TransmitSecurity.StagedHandshakeAdapters
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNestedFrames

/-! Actual nested handshake consumers preserve the staged-origin carrier.
Native state preservation and append-only history are established separately. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged
open AuthenticatedEffects AuthenticatedEffects.CausalJournal RetirementSecurity

theorem nested_initiation (mac : HandshakeMac) : StateSafe
    (NestedPeerRelease.admitInitiationWith CallbackFrames.nested CallbackFrames.admissionRecord mac) :=
  state_quiet (CallbackFrames.initiation_appends mac)
    (CallbackFrames.initiation_quiet selection? (fun _ => rfl) (fun _ => rfl) mac).2
    (CallbackFrames.initiation_erases mac) (fun _ => Native.initiation mac.input)

theorem nested_response (mac : HandshakeMac) : StateSafe
    (NestedPeerRelease.admitResponseWith CallbackFrames.nested CallbackFrames.admissionRecord mac) :=
  state_quiet (CallbackFrames.response_appends mac)
    (CallbackFrames.response_quiet selection? (fun _ => rfl) (fun _ => rfl) mac).2
    (CallbackFrames.response_erases mac) (fun _ => Native.response mac.input)

theorem nested_cookie (msg : Key) : StateSafe
    (NestedPeerRelease.cookieObserved CallbackFrames.nested Event.cookieConsumed msg) :=
  state_quiet (CallbackFrames.cookie_appends msg)
    (CallbackFrames.cookie_quiet selection? (fun _ => rfl) (fun _ => rfl) msg).2
    (CallbackFrames.cookie_erases msg) (fun _ => Native.cookie_consume msg)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
