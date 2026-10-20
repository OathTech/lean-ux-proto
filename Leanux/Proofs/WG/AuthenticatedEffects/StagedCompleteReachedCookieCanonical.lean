import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumerCanonical
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCookieEmissionSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCookieNativeCanonical

/-! Cookie emission uses the original native front, route, captured tunnel prefix, append and receipt, with no TX ticket introduced by the reply. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.HandshakeConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing TransmitSecurity CausalJournal

noncomputable def cookieTunnelShape (mac : HandshakeMac) (msg : Key) (src : SkbSource)
    (e : Endpoint) (bytes : Key) (ds : Nat) (route : Route) : Shape (liftWGObserver
      (CookieEmission.tunnel (fun r=>Event.cookieSocket ⟨mac,msg,src,r⟩) e bytes ds route)) := by
  unfold CookieEmission.tunnel
  repeat' first
    | (consumer_source_head captureWGRun; exact .native (.capturedMetadata _ (PeerMetadata.tunnelReplyShape _ _ _)))
    | (consumer_source_head emitStatePrefix; exact .native (.cookieDatagram _))
    | (consumer_source_head liftWGPrefix
       refine .native (.metadata _ ?_)
       apply PeerMetadata.Shape.access
       apply Access.Shape.write
       exact KeyFrames.world _ (fun _=>rfl))
    | consumer_source_step

noncomputable def cookieSocketShape (mac : HandshakeMac) (msg : Key) (src : SkbSource)
    (args : ProtocolSocket.Args) : Shape (liftWGObserver
      (CookieEmission.socket (fun r=>Event.cookieSocket ⟨mac,msg,src,r⟩) args)) := by
  unfold CookieEmission.socket
  repeat' first
    | (consumer_wg_head CookieRoute.action; exact .native (.cookieRoute _))
    | (consumer_source_head CookieEmission.tunnel; exact cookieTunnelShape _ _ _ _ _ _ _)
    | consumer_source_step

noncomputable def cookieReplyShape (mac : HandshakeMac) (msg : Key) (src : SkbSource)
    (bytes : Key) : Shape (liftWGObserver
      (CookieEmission.reply (fun r=>Event.cookieSocket ⟨mac,msg,src,r⟩) src bytes)) := by
  unfold CookieEmission.reply
  repeat' first
    | (consumer_wg_head replyFront; exact .native (.metadata _ (PeerMetadata.replyFrontShape _)))
    | (consumer_source_head CookieEmission.socket; exact cookieSocketShape _ _ _ _)
    | consumer_source_step

noncomputable def cookieShape (mac : HandshakeMac) (msg : Key) (src : SkbSource) : Shape
    (liftWGObserver (CookieSocket.observed Event.cookieSocket mac msg src)) := by
  rw [CookieEmission.observed_source]
  unfold CookieEmission.observed
  repeat' first
    | (consumer_wg_head cookieMessageCreate; exact .native (.metadata _ (PeerMetadata.cookieMessageShape _ _ _)))
    | (consumer_source_head CookieEmission.reply; exact cookieReplyShape _ _ _ _)
    | consumer_source_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.HandshakeConcrete
