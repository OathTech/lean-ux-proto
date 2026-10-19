import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendDriver
import Leanux.Proofs.WG.AuthenticatedEffects.CookieDispatch

/-! A qualifying input executes the cookie-only continuation of the actual
raw receiver. This counts original append occurrences before any later Stop;
session and keepalive callbacks are arbitrary because this branch cannot call them. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources Cookies
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem afterMac_cookie (session : PeerId → WGPrefix Event Bool)
    (keepalive : PeerId → WGPrefix Event Unit) (msg : Key) (src : SkbSource)
    (w : WGWorld) (a : Ambient) (history : List Event)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    runWGPrefix (afterMacWith (receiveOps session keepalive) msg src true .noCookie) w a history =
      runWGPrefix (cookie msg src) w (cookieReplyEntry msg a) history := by
  have hc : (MacState.noCookie == MacState.withCookie) = false := rfl
  have hn : (MacState.noCookie == MacState.noCookie) = true := rfl
  rcases kind with kind | kind
  all_goals simp [afterMacWith,receiveOps,HandshakeWorker.ops,liftWG_bind_run,WG.orM,WG.andM,
    branch,CounterWindow.branch_run,StateT.run_bind,kind,hc,hn,
    MESSAGE_HANDSHAKE_INITIATION,MESSAGE_HANDSHAKE_RESPONSE,cookieReplyEntry,replyEntry,responseReplyEntry]

theorem qualifying_receive (session : PeerId → WGPrefix Event Bool)
    (keepalive : PeerId → WGPrefix Event Unit) (msg : Key) (src : SkbSource)
    (w : WGWorld) (a : Ambient) (history : List Event)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (qualified : FailedMac2 msg src w a) :
    runWGPrefix (CookieConsumption.receiveWith (fun msg => liftWGPrefix (cookieMessageConsume msg))
      (fun _ => receiveOps session keepalive) msg src) w a history =
      runWGPrefix (cookie msg src) qualified.made (cookieReplyEntry msg qualified.checked) history := by
  have notCookie : (messageType msg == MESSAGE_HANDSHAKE_COOKIE) = false := by
    rcases kind with kind | kind <;> simp [kind,MESSAGE_HANDSHAKE_INITIATION,
      MESSAGE_HANDSHAKE_RESPONSE,MESSAGE_HANDSHAKE_COOKIE]
  unfold CookieConsumption.receiveWith
  rw [liftWG_bind_run]
  simp only [notCookie]
  change runWGPrefix (liftWGPrefix loadPhase >>= _) w (CounterWindow.record a .hsCookie false) history = _
  rw [liftWG_bind_run,qualified.loadRun]
  change runWGPrefix (captureWGRun (cookieValidatePacket msg src true) >>= _) qualified.loaded qualified.loadedAmbient history = _
  change runStatePrefix _ _ _ _ = _
  rw [runStatePrefix_bind]
  rw [show runStatePrefix (captureWGRun (cookieValidatePacket msg src true)) qualified.loaded qualified.loadedAmbient history = _ from
    runWGPrefix_captureWGRun (cookieValidatePacket msg src true) qualified.loaded qualified.loadedAmbient history,
    qualified.validate]
  exact afterMac_cookie session keepalive msg src qualified.made qualified.checked history kind

/-- The exact load and MAC return values used by the native branch suffice;
there is no extra cryptographic-path or initialized-entry premise. -/
theorem checked_receive (session : PeerId → WGPrefix Event Bool)
    (keepalive : PeerId → WGPrefix Event Unit) (msg : Key) (src : SkbSource)
    (w loaded checked : WGWorld) (a b c : Ambient) (history : List Event)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨ messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (loadRun : (loadPhase.run w).run (CounterWindow.record a .hsCookie false) = .ok ((true,loaded),b))
    (macRun : ((cookieValidatePacket msg src true).run loaded).run b = .ok ((.noCookie,checked),c)) :
    runWGPrefix (CookieConsumption.receiveWith (fun msg => liftWGPrefix (cookieMessageConsume msg))
      (fun _ => receiveOps session keepalive) msg src) w a history =
      runWGPrefix (cookie msg src) checked (cookieReplyEntry msg c) history := by
  have notCookie : (messageType msg == MESSAGE_HANDSHAKE_COOKIE) = false := by
    rcases kind with kind | kind <;> simp [kind,MESSAGE_HANDSHAKE_INITIATION,
      MESSAGE_HANDSHAKE_RESPONSE,MESSAGE_HANDSHAKE_COOKIE]
  unfold CookieConsumption.receiveWith
  rw [liftWG_bind_run]
  simp only [notCookie]
  change runWGPrefix (liftWGPrefix loadPhase >>= _) w (CounterWindow.record a .hsCookie false) history = _
  rw [liftWG_bind_run,loadRun]
  change runWGPrefix (captureWGRun (cookieValidatePacket msg src true) >>= _) loaded b history = _
  change runStatePrefix _ _ _ _ = _
  rw [runStatePrefix_bind]
  rw [show runStatePrefix (captureWGRun (cookieValidatePacket msg src true)) loaded b history = _ from
    runWGPrefix_captureWGRun (cookieValidatePacket msg src true) loaded b history,macRun]
  exact afterMac_cookie session keepalive msg src checked c history kind

theorem checked_receive_count (session : PeerId → WGPrefix Event Bool)
    (keepalive : PeerId → WGPrefix Event Unit) (msg : Key) (src : SkbSource)
    (w loaded checked : WGWorld) (a b c : Ambient) (history : List Event)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨ messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (loadRun : (loadPhase.run w).run (CounterWindow.record a .hsCookie false) = .ok ((true,loaded),b))
    (macRun : ((cookieValidatePacket msg src true).run loaded).run b = .ok ((.noCookie,checked),c)) :
    ∃ suffix,
      (runWGPrefix (CookieConsumption.receiveWith (fun msg => liftWGPrefix (cookieMessageConsume msg))
        (fun _ => receiveOps session keepalive) msg src) w a history).2 = history ++ suffix ∧ suffix.length ≤ 1 := by
  rw [checked_receive session keepalive msg src w loaded checked a b c history kind loadRun macRun]
  exact cookie_count msg src checked (cookieReplyEntry msg c) history

/-- A single qualifying received input yields at most one original append,
including a prefix whose socket or later continuation Stops. No source session
or keepalive callback can run on this native cookie-only branch. -/
theorem qualifying_receive_count (session : PeerId → WGPrefix Event Bool)
    (keepalive : PeerId → WGPrefix Event Unit) (msg : Key) (src : SkbSource)
    (w : WGWorld) (a : Ambient) (history : List Event)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (qualified : FailedMac2 msg src w a) :
    ∃ suffix,
      (runWGPrefix (CookieConsumption.receiveWith (fun msg => liftWGPrefix (cookieMessageConsume msg))
        (fun _ => receiveOps session keepalive) msg src) w a history).2 = history ++ suffix ∧
      suffix.length ≤ 1 := by
  rw [qualifying_receive session keepalive msg src w a history kind qualified]
  exact cookie_count msg src qualified.made (cookieReplyEntry msg qualified.checked) history

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
