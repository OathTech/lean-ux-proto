import Leanux.Proofs.WG.AuthenticatedEffects.ConsumerSentFrames
import Leanux.Proofs.WG.AuthenticatedEffects.RejectedDispatch

/-! Native refusal paths compose the actual load, MAC and Noise executions.
No initialized-lifetime hypothesis is needed for the egress projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.WG.Cookies Leanux.Proofs.WG.CounterWindow

theorem receive_initiation_refused_sent (msg : List UInt8) (src : SkbSource) (loaded : Bool)
    (w u q v : WGWorld) (a b c d : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION)
    (load : (loadPhase.run w).run (record a .hsCookie false) = .ok ((loaded,u),b))
    (mac : ((cookieValidatePacket msg src loaded).run u).run b =
      .ok ((authenticatedMac loaded,q),c))
    (refused : ((consumeInitiation msg).run q).run (initiationConsumerEntry loaded c) =
      .ok ((none,v),d)) :
    ((receiveHandshakePacket msg src).run w).run a =
      .ok (((),v),record d .hsInitNoPeer true) ∧ v.sent = w.sent := by
  have loadFrame := (ProjectedAction.iff_run_ambient _ _ _).mp loadPhase_sent
    w _ loaded u b load
  have macFrame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (cookieValidatePacket_sent msg src loaded) u b _ q c mac
  have noiseFrame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (consumeInitiation_sent msg) q _ none v d refused
  exact ⟨receive_initiation_refused msg src loaded w u q v a b c d kind load mac refused,
    noiseFrame.trans (macFrame.trans loadFrame)⟩

theorem receive_response_refused_sent (msg : List UInt8) (src : SkbSource) (loaded : Bool)
    (w u q v : WGWorld) (a b c d : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE)
    (load : (loadPhase.run w).run (record a .hsCookie false) = .ok ((loaded,u),b))
    (mac : ((cookieValidatePacket msg src loaded).run u).run b =
      .ok ((authenticatedMac loaded,q),c))
    (refused : ((consumeResponse msg).run q).run (responseConsumerEntry loaded c) =
      .ok ((none,v),d)) :
    ((receiveHandshakePacket msg src).run w).run a =
      .ok (((),v),record d .hsRespNoPeer true) ∧ v.sent = w.sent := by
  have loadFrame := (ProjectedAction.iff_run_ambient _ _ _).mp loadPhase_sent
    w _ loaded u b load
  have macFrame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (cookieValidatePacket_sent msg src loaded) u b _ q c mac
  have noiseFrame := (ProjectedAction.iff_run_ambient _ _ _).mp
    (consumeResponse_sent msg) q _ none v d refused
  exact ⟨receive_response_refused msg src loaded w u q v a b c d kind load mac refused,
    noiseFrame.trans (macFrame.trans loadFrame)⟩

end Leanux.Proofs.WG.AuthenticatedEffects
