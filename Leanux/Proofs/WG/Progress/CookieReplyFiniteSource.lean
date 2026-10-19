import Leanux.Proofs.WG.Progress.AllocationProgressSource
import Leanux.WG.Receive

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG

/-- The original reply sender with finite allocation evaluation. Uncached
IPv4/IPv6 routing and the lax transmit cut retain their original finite bounds. -/
def sendReply (src : SkbSource) (buffer : List UInt8) : WG.M Unit := do
  if ← branch .replyInSkbNull false then invariant "a cookie reply without an skb"
  let endpoint ← endpointFromSkb src
  if ← branch .replyEndpointErr endpoint.isNone then
    invariant "a cookie reply to an skb that is neither IPv4 nor IPv6"
  let some e := endpoint | invariant "unreachable"
  if ← branch .replyNoMem !(← monadLift (hiddenAllocFinite .replySkb)) then return
  if ← branch .replyInet (e.family == AF_INET) then _ ← send4 e none buffer 0 false
  else if ← branch .replyInet6 (e.family == AF_INET6) then _ ← send6 e none buffer 0 false

/-- Original cookie creation followed by the exact finite reply sender. -/
def sendCookie (msg : List UInt8) (src : SkbSource) : WG.M Unit := do
  let index := u32le msg 4
  let mac1 := (msg.drop (msg.length - 32)).take 16
  sendReply src (← cookieMessageCreate index src mac1)

theorem sendReply_source (src : SkbSource) (buffer : List UInt8) :
    WG.sendBufferAsReplyToSkb src buffer = sendReply src buffer := by
  unfold WG.sendBufferAsReplyToSkb sendReply
  have allocation : (hiddenAlloc .replySkb : WG.M Bool) =
      monadLift (hiddenAllocFinite .replySkb) := by
    change monadLift (AmbientM.hiddenAlloc .replySkb) = _
    rw [hiddenAlloc_finite_source]
  rw [allocation]
  rfl

theorem sendCookie_source (msg : List UInt8) (src : SkbSource) :
    WG.sendHandshakeCookie msg src = sendCookie msg src := by
  unfold WG.sendHandshakeCookie sendCookie
  simp only [sendReply_source]

end Leanux.Proofs.WG.Progress.HandshakeFinite
