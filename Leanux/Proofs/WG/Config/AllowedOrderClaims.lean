import Leanux.Proofs.WG.Config.AllowedOrderInspectionSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.AllowedOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.AllowedIps Configuration Noise
open Leanux.Proofs.Framing Lifetimes Std.Do

theorem original_update_order (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) :
    Campaign2.Observes (peerConfigUpdateSource attrs peer flags psk pid) (fun _=>True)
      (fun entry outcome=>∃result:Inspection,result.outcome=outcome ∧
        Facts attrs peer flags psk pid entry result) := by
  intro w ambient _
  exact ⟨inspection attrs peer flags psk pid w ambient,
    inspection_outcome attrs peer flags psk pid w ambient,
    inspection_facts attrs peer flags psk pid w ambient⟩

theorem original_update_routed_order (tables : FlatTable×FlatTable) (attrs : PeerAttrs)
    (shape : PeerAddressShape attrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) :
    Campaign2.Observes (peerConfigUpdateSource attrs peer flags psk pid) (RoutedTarget tables pid)
      (fun entry outcome=>∃result:Inspection,result.outcome=outcome ∧
        Facts attrs peer flags psk pid entry result ∧ RoutedFacts tables result) := by
  intro w ambient target
  exact ⟨inspection attrs peer flags psk pid w ambient,
    inspection_outcome attrs peer flags psk pid w ambient,
    inspection_facts attrs peer flags psk pid w ambient,
    inspection_routed tables attrs shape peer flags psk pid w ambient target⟩

theorem certificate_allowed_position (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId)
    (entry : Campaign2.Snapshot) (result : Inspection)
    (facts : Facts attrs peer flags psk pid entry result)
    (i : Nat) (e : RoutingCompletion) (ip : AllowedIpAttrs) (ret : Int)
    (selected : (allowedEvents result.completions)[i]?=some e)
    (call : e.call=.allowedIp pid ip ret) :
    (attrs.allowedIps.getD [])[i]?=some (.attrs ip) :=
  facts.2.1.allowed_partial.position i e ip ret selected call

theorem certificate_negative_last (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId)
    (entry : Campaign2.Snapshot) (result : Inspection)
    (facts : Facts attrs peer flags psk pid entry result)
    (i : Nat) (e : RoutingCompletion) (ip : AllowedIpAttrs) (ret : Int)
    (selected : (allowedEvents result.completions)[i]?=some e)
    (call : e.call=.allowedIp pid ip ret) (negative : ret<0) :
    i+1=(allowedEvents result.completions).length :=
  facts.2.1.allowed_partial.negative_last i e ip ret selected call negative

end Leanux.Proofs.WG.Config.AllowedOrder
