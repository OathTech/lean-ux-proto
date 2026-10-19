import Leanux.Proofs.WG.Config.ScalarTailModel

/-! The cache-reset timestamp is outside the exact peer scalar observation; full Endpoint remains included. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarTail
open Leanux Leanux.WG Noise Std.Do
open Queues Queues.RxCredits Leanux.Proofs.Framing Lifetimes
open PeerScalarRetention ScalarFinish

theorem prefixCell_reset (p : Peer) (psk : Option Key) (endpoint : Option EndpointAttr)
    (reset : Option UInt64) :
    cell (ScalarPrefix.effectPeer p psk endpoint reset)=prefixCell p psk endpoint := by
  cases endpoint with
  | none=>rfl
  | some attr=>
    unfold ScalarPrefix.effectPeer endpointAttributePeer prefixCell
    cases decoded : endpointAttribute attr with
    | none=>simp only [ScalarPrefix.effectPeer,endpointAttributePeer,decoded]
    | some ep=>
      simp only [ScalarPrefix.effectPeer,endpointAttributePeer,decoded]
      unfold endpointStoredPeer
      split
      · rfl
      · cases reset <;> rfl

end Leanux.Proofs.WG.Config.ScalarTail
