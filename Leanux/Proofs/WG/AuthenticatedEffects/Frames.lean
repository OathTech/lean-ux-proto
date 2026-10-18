import Leanux.Proofs.WG.AuthenticatedEffects.CookieDispatch

/-! Local Noise/session preservation for the two cookie-only dispatch arms. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.WG.Cookies Leanux.Proofs.Framing
open Leanux.Proofs.WG.Lifetimes

theorem qualifying_rejected_noise (msg : List UInt8) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION ∨
      messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (h : FailedMac2 msg src w a)
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((), v), b)) :
    noiseView v = noiseView w := by
  rw [qualifying_rejected_run msg src w a kind h] at run
  have hs := (ProjectedAction.iff_run_ambient _ _ _).mp (sendHandshakeCookie_frame msg src)
    h.made (cookieReplyEntry msg h.checked) () v b run
  have hc := (ProjectedAction.iff_run_ambient _ _ _).mp (makeCookie_frame src)
    h.loaded _ h.cookie h.made h.madeAmbient h.cookieRun
  have hl := (ProjectedAction.iff_run_ambient _ _ _).mp loadPhase_sameStore
    w _ true h.loaded h.loadedAmbient h.loadRun
  exact hs.trans (hc.trans (congrArg viewOfStore hl))

end Leanux.Proofs.WG.AuthenticatedEffects
