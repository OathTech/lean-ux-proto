import Leanux.Proofs.WG.Configuration.PeerTailRouting
import Leanux.Proofs.WG.AllowedIps.RoutingSendFrames

/-! Complete original peer-configuration tail with a failure-retaining routing
completion journal. Concrete send/cleanup frames allow peer deletion; only the
allowed-IP loop maintains its insertion target's residency. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.AllowedIps Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000

theorem peerTailFinishSource_routing (a : PeerAttrs) (peer : Option PeerId)
    (pid : PeerId) (ret : Int) : RetainsRoutingCall (peerTailFinishSource a peer pid ret) := by
  apply ProjectedAction.of_wp
  intro s
  let P := RetainsRouting s
  have hg := routing_getPeer P pid
  have hs := fun p => routing_setPeer P pid p
  have hk := RetainsRoutingCall.wp (sendKeepalive_routing pid) s
  have ht := RetainsRoutingCall.wp (sendStagedPackets_routing pid) s
  have hp := RetainsRoutingCall.wp (peerPut_retainsRouting peer) s
  mvcgen [peerTailFinishSource, hg, hs, hk, ht, hp, WG.andM, getDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold routingView at *; simp_all [routingState])
  all_goals try assumption
  all_goals subst s
  all_goals try exact RetainsRouting.refl _

def peerConfigTailObserved (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    WGPrefix RoutingCompletion Int :=
  peerAllowedIpsObservedWG a peer pid (fun ret => liftWGPrefix (peerTailFinishSource a peer pid ret))

theorem peerConfigTailObserved_erases (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    ErasesStatePrefix (peerConfigTailObserved a peer pid) (peerConfigTailSource a peer pid) := by
  rw [peerConfigTailSource_factor]
  exact peerAllowedIpsObservedWG_erases a peer pid _ _ (fun _ => erasesStatePrefix_lift _)

theorem peerConfigTailObserved_spec (initial : FlatTable × FlatTable)
    (a : PeerAttrs) (shape : PeerAddressShape a) (peer : Option PeerId) (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
      (peerConfigTailObserved a peer pid) (fun _ h w _ => CompletionState initial h w) := by
  apply peerAllowedIpsObservedWG_spec initial a shape peer pid
  intro ret
  exact (completion_lift_retains_wg initial _ (peerTailFinishSource_routing a peer pid ret)).consequence
    (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)

end Leanux.Proofs.WG.Configuration
