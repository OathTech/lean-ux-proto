import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptInitialized
import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueCookieReceive

/-! The native cookie exception is strictly smaller than its own accepted input. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Receipts
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem initialized_cookie_size (trace : Runner.Trace) (placeholders : Bool)
    (before after : List Event) (receipt : CookieSocket.Receipt)
    (position : (runPrefixOuter (execute trace placeholders) []).2 =
      before ++ .cookieSocket receipt :: after) :
    receipt.Valid ∧ receipt.Qualifying ∧ receipt.datagram.bytes.length < receipt.input.length := by
  have qualified := initialized_cookie_qualified trace placeholders before after receipt position
  have header := RetirementSecurity.HandshakeLengths.Cookie.initialized_cookie
    trace placeholders before after receipt position
  refine ⟨qualified.1,qualified.2.1,?_⟩
  rw [qualified.1.2.2.2.1]
  exact TransmitSecurity.HeaderLength.larger_than_cookie header qualified.2.2

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Receipts
