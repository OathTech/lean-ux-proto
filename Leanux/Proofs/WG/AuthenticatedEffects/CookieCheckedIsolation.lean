import Leanux.Proofs.WG.AuthenticatedEffects.MacWorldFrames
import Leanux.Proofs.WG.AuthenticatedEffects.Frames

/-! Session isolation under the exact load/MAC return values used by the cookie
branch. No reconstructed cryptographic-path witness is required. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CookieChecked
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Cookies
open Leanux.Proofs.WG.CounterWindow

theorem native (msg : Key) (src : SkbSource) (w loaded checked : WGWorld) (a b c : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨ messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (loadRun : (loadPhase.run w).run (record a .hsCookie false) = .ok ((true,loaded),b))
    (macRun : ((cookieValidatePacket msg src true).run loaded).run b = .ok ((.noCookie,checked),c)) :
    ((receiveHandshakePacket msg src).run w).run a =
      ((sendHandshakeCookie msg src).run checked).run (cookieReplyEntry msg c) := by
  have notCookie : (messageType msg == MESSAGE_HANDSHAKE_COOKIE) = false := by
    rcases kind with kind | kind <;> simp [kind,MESSAGE_HANDSHAKE_INITIATION,
      MESSAGE_HANDSHAKE_RESPONSE,MESSAGE_HANDSHAKE_COOKIE]
  rw [receive_factor]
  simp only [StateT.run_bind,notCookie,branch,StateT.run_monadLift,StateT.run_pure,
    monadLift_self,branch_run,except_ok_bind,pure_bind,Bool.false_eq_true,↓reduceIte,loadRun,macRun]
  rcases kind with init | response
  · simpa only [cookieReplyEntry,init,↓reduceIte] using afterMac_noCookie msg src checked c init
  · have distinct : messageType msg ≠ MESSAGE_HANDSHAKE_INITIATION := by
      simp [response,MESSAGE_HANDSHAKE_RESPONSE,MESSAGE_HANDSHAKE_INITIATION]
    simpa only [cookieReplyEntry,distinct,↓reduceIte] using response_afterMac_cookie msg src checked c response

theorem isolation (msg : Key) (src : SkbSource) (w loaded checked v : WGWorld) (a b c d : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨ messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (loadRun : (loadPhase.run w).run (record a .hsCookie false) = .ok ((true,loaded),b))
    (macRun : ((cookieValidatePacket msg src true).run loaded).run b = .ok ((.noCookie,checked),c))
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),d)) :
    noiseView v = noiseView w := by
  rw [native msg src w loaded checked a b c kind loadRun macRun] at run
  have sent := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (sendHandshakeCookie_frame msg src) checked (cookieReplyEntry msg c) () v d run
  have mac := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (MacWorld.validate msg src true) loaded b .noCookie checked c macRun
  have macNoise : noiseView checked = noiseView loaded := by
    have erase (world : WGWorld) : noiseView (MacWorld.view world) = noiseView world := by
      cases hd : world.dev <;> simp [noiseView,viewOfStore,wgStoreView,MacWorld.view,hd,cookieDevice,scrub]
    have projected := congrArg noiseView mac
    simpa only [erase] using projected
  have load := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    loadPhase_sameStore w _ true loaded b loadRun
  exact sent.trans (macNoise.trans (congrArg viewOfStore load))

end Leanux.Proofs.WG.AuthenticatedEffects.CookieChecked
