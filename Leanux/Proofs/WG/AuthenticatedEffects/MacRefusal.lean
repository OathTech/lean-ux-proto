import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeQuietFrames

/-! Invalid and rate-limited MAC outcomes terminate the original receive
before either Noise consumer. Only the already-named cookie/load bookkeeping
can have occurred at this cut; no response or peer protocol effect follows. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow
open Leanux.Proofs.WG.Cookies Leanux.Proofs.WG.Lifetimes

theorem afterMac_ratelimited (msg : Key) (src : SkbSource) (loaded : Bool)
    (w : WGWorld) (a : Ambient) :
    ((afterMac msg src loaded .ratelimited).run w).run a =
      .ok (((),w),invalidDropEntry loaded a) := by
  have noCookie : (MacState.ratelimited == MacState.noCookie) = false := rfl
  have withCookie : (MacState.ratelimited == MacState.withCookie) = false := rfl
  cases loaded <;>
    simp [afterMac,noCookie,withCookie,WG.orM,WG.andM,StateT.run_bind,branch,branch_run,
      invalidDropEntry,dropEntry]

theorem receive_mac_refused (msg : Key) (src : SkbSource) (loaded : Bool) (state : MacState)
    (w u v : WGWorld) (a b c : Ambient)
    (notCookie : messageType msg ≠ MESSAGE_HANDSHAKE_COOKIE)
    (load : (loadPhase.run w).run (record a .hsCookie false) = .ok ((loaded,u),b))
    (mac : ((cookieValidatePacket msg src loaded).run u).run b = .ok ((state,v),c))
    (refused : state = .invalid ∨ state = .ratelimited) :
    ((receiveHandshakePacket msg src).run w).run a =
      .ok (((),v),invalidDropEntry loaded c) ∧
      handshakeQuietView v = handshakeQuietView w ∧ v.sent = w.sent := by
  have kind : (messageType msg == MESSAGE_HANDSHAKE_COOKIE) = false := by simpa using notCookie
  have loadQuiet := (ProjectedAction.iff_run_ambient _ _ _).mp
    (loadPhase_sameStore.factor quietPeerStore) w _ loaded u b load
  have macQuiet := (ProjectedAction.iff_run_ambient _ _ _).mp
    (cookieValidatePacket_quiet msg src loaded) u b state v c mac
  have loadSent := (ProjectedAction.iff_run_ambient _ _ _).mp loadPhase_sent w _ loaded u b load
  have macSent := (ProjectedAction.iff_run_ambient _ _ _).mp
    (cookieValidatePacket_sent msg src loaded) u b state v c mac
  refine ⟨?_,macQuiet.trans loadQuiet,macSent.trans loadSent⟩
  rw [receive_factor]
  simp only [StateT.run_bind,kind,branch,StateT.run_monadLift,StateT.run_pure,
    monadLift_self,branch_run,except_ok_bind,pure_bind,Bool.false_eq_true,↓reduceIte,load,mac]
  rcases refused with rfl | rfl
  · exact afterMac_invalid_any msg src v c loaded
  · exact afterMac_ratelimited msg src loaded v c

end Leanux.Proofs.WG.AuthenticatedEffects
