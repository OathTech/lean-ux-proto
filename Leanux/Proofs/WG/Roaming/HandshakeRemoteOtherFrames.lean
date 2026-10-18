import Leanux.Proofs.WG.Roaming.HandshakeRemoteFrames
import Leanux.Proofs.WG.Roaming.CookieEndpointClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Lifetimes Framing TimerDiscipline Std.Do

theorem rateLimitPrefix_remotes (msg : List UInt8) (src : SkbSource) :
    SameView destinationAt (rateLimitPrefix msg src) :=
  (show SameView destinationAt (branch .hsCookie false : WG.M Bool) from
    fun entry => hoare_liftAmbient (AmbientM.branch .hsCookie false)
      (fun g => destinationAt g = entry)).bind (fun _ =>
    responseLoad_remotes.bind (fun loaded =>
      (sameCookie_remotes _ (cookieValidatePacket_sameCookie msg src loaded)).bind
        (fun value => by intro entry; exact preserves_pure _)))

theorem rateLimitSuffix_other_remotes (msg : List UInt8) (src : SkbSource)
    (input : Bool × MacState)
    (notInit : messageType msg ≠ MESSAGE_HANDSHAKE_INITIATION)
    (notResponse : messageType msg ≠ MESSAGE_HANDSHAKE_RESPONSE) :
    SameView destinationAt (rateLimitSuffix msg src input) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final after run
  obtain ⟨loaded,mac⟩ := input
  have initFalse := beq_eq_false_iff_ne.mpr notInit
  have responseFalse := beq_eq_false_iff_ne.mpr notResponse
  cases loaded <;> cases mac <;>
    simp [rateLimitSuffix,WG.andM,WG.orM,branch,AmbientM.branch,
      initFalse,responseFalse,invariant,AmbientM.invariant] at run
  all_goals obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
  all_goals rfl

theorem receiveHandshakePacket_other_remotes (msg : List UInt8) (src : SkbSource)
    (notInit : messageType msg ≠ MESSAGE_HANDSHAKE_INITIATION)
    (notResponse : messageType msg ≠ MESSAGE_HANDSHAKE_RESPONSE) :
    SameView destinationAt (receiveHandshakePacket msg src) := by
  by_cases cookie : messageType msg = MESSAGE_HANDSHAKE_COOKIE
  · rw [receiveHandshakePacket_cookie_source msg src cookie]
    exact (show SameView destinationAt (branch .hsCookie true : WG.M Bool) from
      fun entry => hoare_liftAmbient (AmbientM.branch .hsCookie true)
        (fun g => destinationAt g = entry)).bind (fun _ =>
      endpoint_frame_remotes _ (cookieMessageConsume_endpoints msg))
  · rw [receiveHandshakePacket_rateLimit_factor msg src cookie]
    exact (rateLimitPrefix_remotes msg src).bind (fun input =>
      rateLimitSuffix_other_remotes msg src input notInit notResponse)


end Leanux.Proofs.WG.Roaming
