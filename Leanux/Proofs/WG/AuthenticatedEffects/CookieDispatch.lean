import Leanux.Proofs.WG.Cookies.Load

/-! The actual cookie-only continuation for either handshake input kind.
These local equations retain the original Stop, rather than asserting that
the socket path completes. They do not assert initialized queue provenance. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.WG.Cookies Leanux.Proofs.Framing
open Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.WG.CounterWindow

def responseReplyEntry (a : Ambient) : Ambient :=
  record (record (record (record (record (record (record (record a
    .hsLoadedOperand true) .hsLoadedCookieOk false) .hsNotLoaded false)
    .hsNeedsCookieLoaded true) .hsNeedsCookieMac true)
    .hsSwitchInitiation false) .hsSwitchResponse true) .hsRespNeedsCookie true

theorem response_afterMac_cookie (msg : List UInt8) (src : SkbSource)
    (w : WGWorld) (a : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    ((afterMac msg src true .noCookie).run w).run a =
      ((sendHandshakeCookie msg src).run w).run (responseReplyEntry a) := by
  have hc : (MacState.noCookie == MacState.withCookie) = false := rfl
  have hn : (MacState.noCookie == MacState.noCookie) = true := rfl
  simp [afterMac, hc, hn, WG.orM, WG.andM, StateT.run_bind, branch, branch_run,
    kind, MESSAGE_HANDSHAKE_INITIATION, MESSAGE_HANDSHAKE_RESPONSE, responseReplyEntry]

theorem response_rejected_run (msg : List UInt8) (src : SkbSource)
    (w : WGWorld) (a : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) (h : FailedMac2 msg src w a) :
    ((receiveHandshakePacket msg src).run w).run a =
      ((sendHandshakeCookie msg src).run h.made).run (responseReplyEntry h.checked) := by
  rw [receive_factor]
  simp only [StateT.run_bind, kind, MESSAGE_HANDSHAKE_RESPONSE, MESSAGE_HANDSHAKE_COOKIE,
    Nat.reduceBEq, branch, StateT.run_monadLift, StateT.run_pure, monadLift_self, branch_run,
    except_ok_bind, pure_bind, Bool.false_eq_true, ↓reduceIte, h.loadRun, h.validate]
  exact response_afterMac_cookie msg src h.made h.checked kind

def cookieReplyEntry (msg : List UInt8) (a : Ambient) : Ambient :=
  if messageType msg = MESSAGE_HANDSHAKE_INITIATION then replyEntry a else responseReplyEntry a

theorem qualifying_rejected_run (msg : List UInt8) (src : SkbSource)
    (w : WGWorld) (a : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (h : FailedMac2 msg src w a) :
    ((receiveHandshakePacket msg src).run w).run a =
      ((sendHandshakeCookie msg src).run h.made).run (cookieReplyEntry msg h.checked) := by
  rcases kind with init | response
  · simpa only [cookieReplyEntry, init, ↓reduceIte] using receive_rejected_run msg src w a init h
  · have distinct : messageType msg ≠ MESSAGE_HANDSHAKE_INITIATION := by
      simp [response, MESSAGE_HANDSHAKE_RESPONSE, MESSAGE_HANDSHAKE_INITIATION]
    simpa only [cookieReplyEntry, distinct, ↓reduceIte] using response_rejected_run msg src w a response h

end Leanux.Proofs.WG.AuthenticatedEffects
