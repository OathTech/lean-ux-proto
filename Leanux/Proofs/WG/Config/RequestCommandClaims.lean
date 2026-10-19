import Leanux.Proofs.WG.Config.RequestCommandSource
import Leanux.Proofs.WG.Config.RequestCommandEffects
import Leanux.Proofs.WG.Config.RequestOrderClaims
import Leanux.Proofs.WG.Config.CommandOrderClaims

/-! Arbitrary device-request certificates expose nested routing order for every completed peer command, including receipts retained before a later Stop. An interrupted peer call has no completed outer receipt here; its internal prefix is not reconstructed. Routing effects require the explicit representation and shape domain at the actual peer-entry receipt. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.AllowedIps Configuration Noise

theorem certificate_peer_command (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs entry result)
    (i : Nat) (r : Receipt) (p : PeerAttrs)
    (selected : (peerReceipts result.receipts)[i]?=some r) (kind : r.kind=.peer p) :
    (attrs.peers.getD [])[i]?=some (.attrs p) ∧ ∃nested,PeerCommandFacts r p nested := by
  have member : r∈result.receipts :=
    (List.mem_filter.mp (List.mem_of_getElem? selected)).1
  exact ⟨certificate_peer_position attrs entry result facts i r p selected kind,
    valid_peer_command attrs r p (facts.1.2.1 r member) kind⟩

theorem certificate_nested_commands (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs entry result) :
    NestedCommands attrs result :=
  fun i r p selected kind=>certificate_peer_command attrs entry result facts i r p selected kind

theorem original_request_nested_commands (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (fun _=>True)
      (fun entry outcome=>∃result:Inspection,result.outcome=outcome ∧
        Certificate attrs entry result ∧ NestedCommands attrs result) := by
  intro w ambient _
  have facts:=inspection_certificate attrs w ambient
  exact ⟨inspection attrs w ambient,inspection_outcome attrs w ambient,facts,
    certificate_nested_commands attrs _ _ facts⟩

theorem certificate_peer_command_routed (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs entry result)
    (i : Nat) (r : Receipt) (p : PeerAttrs)
    (selected : (peerReceipts result.receipts)[i]?=some r) (kind : r.kind=.peer p)
    (tables : FlatTable×FlatTable) (shape : PeerAddressShape p)
    (routed : RoutedView (r.before.wg.device.map routingState) tables) :
    (attrs.peers.getD [])[i]?=some (.attrs p) ∧
      ∃nested,PeerCommandFacts r p nested ∧ AllowedOrder.RoutedFacts tables nested := by
  obtain ⟨position,nested,point⟩:=certificate_peer_command attrs entry result facts i r p selected kind
  exact ⟨position,nested,point,point.1.routed r p nested tables shape routed⟩

theorem nested_allowed_position (r : Receipt) (p : PeerAttrs) (nested : AllowedOrder.Inspection)
    (point : PeerCommandFacts r p nested) (i : Nat) (e : RoutingCompletion)
    (pid : PeerId) (ip : AllowedIpAttrs) (ret : Int)
    (selected : (AllowedOrder.allowedEvents nested.completions)[i]?=some e)
    (call : e.call=.allowedIp pid ip ret) :
    (p.allowedIps.getD [])[i]?=some (.attrs ip) :=
  CommandOrder.certificate_allowed_position p r.before nested point.2.2 i e pid ip ret selected call

theorem nested_negative_last (r : Receipt) (p : PeerAttrs) (nested : AllowedOrder.Inspection)
    (point : PeerCommandFacts r p nested) (i : Nat) (e : RoutingCompletion)
    (pid : PeerId) (ip : AllowedIpAttrs) (ret : Int)
    (selected : (AllowedOrder.allowedEvents nested.completions)[i]?=some e)
    (call : e.call=.allowedIp pid ip ret) (negative : ret<0) :
    i+1=(AllowedOrder.allowedEvents nested.completions).length :=
  CommandOrder.certificate_negative_last p r.before nested point.2.2 i e pid ip ret selected call negative

theorem nested_negative_return (r : Receipt) (p : PeerAttrs) (nested : AllowedOrder.Inspection)
    (point : PeerCommandFacts r p nested) (e : RoutingCompletion)
    (member : e∈AllowedOrder.allowedEvents nested.completions)
    (pid : PeerId) (ip : AllowedIpAttrs) (ret : Int)
    (call : e.call=.allowedIp pid ip ret) (negative : ret<0) : r.result=ret := by
  have nonempty : nested.completions≠[] := by
    intro empty
    simp only [empty,AllowedOrder.allowedEvents,List.filter_nil] at member
    cases member
  obtain ⟨target,effective,_,_,finished⟩:=
    CommandOrder.certificate_selected p r.before nested point.2.2 nonempty
  rw [point.2.1] at finished
  exact update_negative_result finished e member pid ip ret call negative

theorem certificate_nested_negative_peer_last (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs entry result)
    (i : Nat) (r : Receipt) (p : PeerAttrs)
    (selected : (peerReceipts result.receipts)[i]?=some r)
    (nested : AllowedOrder.Inspection) (point : PeerCommandFacts r p nested)
    (e : RoutingCompletion) (member : e∈AllowedOrder.allowedEvents nested.completions)
    (pid : PeerId) (ip : AllowedIpAttrs) (ret : Int)
    (call : e.call=.allowedIp pid ip ret) (negative : ret<0) :
    r.result=ret ∧ ∃before,peerReceipts result.receipts=before++[r] := by
  have code:=nested_negative_return r p nested point e member pid ip ret call negative
  exact ⟨code,request_negative_peer_last attrs result.receipts facts.1.2.2.1 r
    (List.mem_of_getElem? selected) (by rw [code];exact negative)⟩

end Leanux.Proofs.WG.Config.RequestOrder
