import Leanux.Proofs.WG.AuthenticatedEffects.Frames
import Leanux.Proofs.WG.AuthenticatedEffects.ReplyBinding
import Leanux.Proofs.WG.AuthenticatedEffects.Emission
import Leanux.Proofs.WG.AuthenticatedEffects.CryptoSizes

/-! T3 local cookie exception tranche. These claims establish the original
cookie-only dispatch, bounded construction/reply attempts and session frame.
Normal native receives now have an actual emitted-datagram bound and source/bytes
binding. Fixed cookie length, emitted-event prefixes through Stop, and whole-run
causal closure remain separate obligations; attempt receipts are not transmissions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.Cookies

/-- Security: qualifying invalid-MAC2 initiations and responses execute only the
original cookie-reply suffix. The continuous `FailedMac2` witness supplies the
actual under-load/MAC checks; this local claim covers both normal and Stop results. -/
theorem cookie_exception_original_path (msg : List UInt8) (src : SkbSource)
    (w : WGWorld) (a : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (h : FailedMac2 msg src w a) :
    ((receiveHandshakePacket msg src).run w).run a =
      ((sendHandshakeCookie msg src).run h.made).run (cookieReplyEntry msg h.checked) :=
  qualifying_rejected_run msg src w a kind h

/-- Security: the qualifying unauthenticated cookie exception cannot modify the
Noise/session projection on a normally completed native receive. Cookie-secret
maintenance and transmission statistics lie outside this named R6 projection. -/
theorem cookie_exception_preserves_sessions (msg : List UInt8) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (h : FailedMac2 msg src w a)
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),b)) :
    noiseView v = noiseView w := qualifying_rejected_noise msg src w v a b kind h run

/-- Security: a native cookie-reply invocation completes at most one cookie
construction, with the exact original input and source. Its receipt survives a
later Stop; this bounds construction attempts, not emitted datagrams. -/
theorem cookie_exception_one_creation (msg : List UInt8) (src : SkbSource)
    (w : WGWorld) (a : Ambient) (history : List CookieAttempt) :
    ∃ suffix, (runWGPrefix (cookieObserved msg src) w a history).2 = history ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix, r.input = msg ∧ r.source = src ∧ r.Valid :=
  cookieObserved_receipts msg src w a history

/-- Security: the original cookie reply reaches at most one guarded socket-call
attempt, carrying exactly the supplied source and cookie bytes. Its receipt is
retained even if that socket call stops; successful emission is not assumed. -/
theorem cookie_exception_one_socket_attempt (src : SkbSource) (bytes : List UInt8)
    (w : WGWorld) (a : Ambient) (history : List ReplyAttempt) :
    ∃ suffix, (runWGPrefix (replyObserved src bytes) w a history).2 = history ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix, r.source = src ∧ r.bytes = bytes ∧ r.Valid :=
  replyObserved_receipts src bytes w a history

/-- Security: the qualifying unauthenticated cookie exception emits at most one
actual datagram, addressed to the triggering source and carrying exactly the
original cookie construction's bytes. This is a normal native receive claim;
it does not yet establish length 64 or whole-run authenticated causal closure. -/
theorem cookie_exception_transmission_bound (msg : List UInt8) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (h : FailedMac2 msg src w a)
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),b)) :
    ∃ bytes u c,
      ((cookieMessageCreate (u32le msg 4) src ((msg.drop (msg.length - 32)).take 16)).run h.made).run
        (cookieReplyEntry msg h.checked) = .ok ((bytes,u),c) ∧
      ReplyEmission src bytes w.sent v.sent :=
  qualifying_cookie_emission msg src w v a b kind h run

end Leanux.Proofs.WG.AuthenticatedEffects
