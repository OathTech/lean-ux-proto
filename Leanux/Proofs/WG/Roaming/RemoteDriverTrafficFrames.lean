import Leanux.Proofs.WG.Roaming.RemoteDriverDeferredSource
import Leanux.Proofs.WG.Roaming.RemoteDriverPollSource
import Leanux.Proofs.WG.Roaming.ReceiveIngressClaims
import Leanux.Proofs.WG.Noise.PendingTrafficFrames
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation





set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteDriver
open Leanux Leanux.WG Noise Queues Lifetimes Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem wg_store_inv (entry : RemoteMap) (h : List Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (pre : Inv entry h w) : Inv entry h v := by
  have dev : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev same
  have remote : destinationAt v.wg = destinationAt w.wg := by
    funext pid
    simp only [destinationAt, Noise.peerAt, dev]
  change RemoteCovered entry Cause h (destinationAt v.wg) ∧ Safe h
  rw [remote]
  exact pre

namespace Traffic

theorem receive_frame (msg : List UInt8) (src : SkbSource) :
    SameView destinationAt (wgReceive msg src) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient value final after run
  exact endpointMap_destinations
    ((wgReceive_preserves_endpoints msg src (Campaign2.snapshot g ambient)
      g ambient value final after rfl run).1)

end Traffic
end Leanux.Proofs.WG.Roaming.RemoteDriver
