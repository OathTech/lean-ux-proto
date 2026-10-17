import Leanux.Proofs.WG.Index.ReceiveOperations

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG

/-- The original type-3 receive call records its cookie decision and consumes
the message, then returns. Equality retains every original error and state;
the MAC-admission, cookie-reply and authenticated suffix are not executed. -/
theorem receiveHandshakePacket_cookie_source (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_COOKIE) :
    receiveHandshakePacket msg src = (do
      _ ← (branch .hsCookie true : WG.M Bool)
      cookieMessageConsume msg) := by
  rw [← Index.receivePacket_source]
  unfold Index.receivePacketSource
  simp only [kind,beq_self_eq_true]
  funext g ambient
  let logged := {ambient with steps := ambient.steps.push {decision := .hsCookie,outcome := true,netRx := ambient.netRxSection}}
  change (cookieMessageConsume msg g logged >>= fun ((value,current),inputs) =>
    Except.ok (((),current),inputs)) = cookieMessageConsume msg g logged
  cases actual : cookieMessageConsume msg g logged with
  | error stop => rfl
  | ok out =>
    obtain ⟨⟨value,current⟩,inputs⟩ := out
    cases value
    rfl

end Leanux.Proofs.WG.Roaming
