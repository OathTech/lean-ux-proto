import Leanux.Proofs.WG.Progress.RateLimitFiniteSource
import Leanux.Proofs.WG.Progress.CookieReplyFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG

/-- Exact finite evaluation of the complete rate limiter, preserving each
source-family, capacity, allocation and record-error outcome. -/
theorem original_ratelimiter_finite (src : SkbSource) :
    Campaign2.AgreesOn (fun _ => True) (WG.ratelimiterAllow src) (ratelimiter src) := by
  rw [ratelimiter_source]
  intro g ambient pre
  rfl

/-- Exact finite evaluation of every cookie validation path, including
MAC refusal, secret rotation, rate limiting and allocation failure. -/
theorem original_validateCookie_finite (msg : List UInt8) (src : SkbSource)
    (checkCookie : Bool) :
    Campaign2.AgreesOn (fun _ => True) (WG.cookieValidatePacket msg src checkCookie)
      (validateCookie msg src checkCookie) := by
  rw [validateCookie_source]
  intro g ambient pre
  rfl

/-- Exact finite evaluation of the original reply sender. Invalid endpoints,
allocation failure, socket refusal and routing Stops remain actual outcomes. -/
theorem original_sendReply_finite (src : SkbSource) (buffer : List UInt8) :
    Campaign2.AgreesOn (fun _ => True) (WG.sendBufferAsReplyToSkb src buffer)
      (sendReply src buffer) := by
  rw [sendReply_source]
  intro g ambient pre
  rfl

/-- Exact finite evaluation of cookie creation followed by the original
reply path. This does not assert that a datagram is sent successfully. -/
theorem original_sendCookie_finite (msg : List UInt8) (src : SkbSource) :
    Campaign2.AgreesOn (fun _ => True) (WG.sendHandshakeCookie msg src)
      (sendCookie msg src) := by
  rw [sendCookie_source]
  intro g ambient pre
  rfl
end Leanux.Proofs.WG.Progress.HandshakeFinite
