import Leanux.Proofs.WG.Config.ScalarTailEffects

/-! Pure refcount-acquisition congruence for the stamped scalar projection. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarCommand
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration
open PeerScalarRetention
theorem prefixCell_acquire (p : Peer) (psk : Option Key) (endpoint : Option EndpointAttr) :
    ScalarTail.prefixCell {p with refcount:=p.refcount+1} psk endpoint=
      ScalarTail.prefixCell p psk endpoint := by
  cases psk <;> cases endpoint
  all_goals simp only [ScalarTail.prefixCell,ScalarPrefix.effectPeer,ScalarPrefix.keyedPeer]
  all_goals first
    | rfl
    | (unfold endpointAttributePeer endpointStoredPeer
       split
       · rfl
       · split <;> rfl)

end Leanux.Proofs.WG.Config.ScalarCommand
