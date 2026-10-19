import Leanux.Proofs.WG.Configuration.RoutingRunner
import Leanux.Proofs.WG.Configuration.InitializedJoint
import Leanux.Proofs.WG.Packets.PublicationRunner
import Leanux.Proofs.WG.Packets.PublicationEntries

/-! Initialized incoming authorization at one specified Stack-entry position.
The original runner supplies packet and routing evidence; no entry invariant
or normal final result is an input. -/
namespace Leanux.Proofs.WG.InitializedEntries
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues PublicationIdentity AllowedIps Configuration

/-- One selected entry has its actual earlier consume and configured publication,
with the source winner computed at that consume's strict earlier routing prefix. -/
theorem entered (trace : Runner.Trace) (shape : TraceAddressShape trace) (placeholders : Bool)
    (pre post : List RoutingJoint.Event) (e : RxJoint.Entry)
    (position : (runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).2 =
      pre ++ .rx (.entered e) :: post) :
    ∃ (receipt : RxDisposition.ConsumeReceipt), ∃ before between afterBuffer beforeDecrypt afterDecrypt,
      ∃ (decrypt : WGRunWitness (RxPacket × Option RxPacket)), ∃ out pid published ambient,
      pre = before ++ .rx (.consumed e.tag.occurrence e.tag.skb e.stamp receipt) ::
        (between ++ .rx (.buffered e) :: afterBuffer) ∧
      before = beforeDecrypt ++ .rx (.rx (.decrypt e.tag.skb decrypt)) :: afterDecrypt ∧
      e.origin = some receipt ∧ receipt.run.value = some e.tag.bytes ∧
      Published e.tag.skb decrypt out pid published ambient ∧
      ConsumeCertificate (Origins.HistorySupport.sessions (beforeDecrypt.filterMap RoutingJoint.rxEvent))
        e.tag.skb decrypt out pid published e.stamp receipt ∧
      ∃ v4 : Bool,
        ipTunnelParseProtocol e.tag.bytes = (if v4 then 4 else 6) ∧
        ipTunnelParseProtocol receipt.packet.bytes = (if v4 then 4 else 6) ∧
        PeerWinner (rootWidth v4) (sourceAddress v4 e.tag.bytes)
          (selectedFlat v4 (completionFold (before.filterMap RoutingJoint.routingEvent) ([],[])))
          (some receipt.peer) ∧
        sourceAddress v4 e.tag.bytes = sourceAddress v4 receipt.packet.bytes := by
  exact PublicationEntries.entered_authorized
    (RoutingPosition.executeTrace_checks trace shape placeholders).2.1
    (PublicationRunner.joint trace placeholders).2
    (RoutingPosition.Runner.executeTrace trace shape placeholders).2 position


/-- Successful public parsing supplies the address-shape facts used by routing;
all later returned or stopped outcomes use the same actual initialized journal. -/
theorem parsed_entered (json : Lean.Json) (trace : Runner.Trace)
    (parsed : Runner.parseTrace json = .ok trace) (placeholders : Bool)
    (pre post : List RoutingJoint.Event) (e : RxJoint.Entry)
    (position : (runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).2 =
      pre ++ .rx (.entered e) :: post) :
    ∃ (receipt : RxDisposition.ConsumeReceipt), ∃ before between afterBuffer beforeDecrypt afterDecrypt,
      ∃ (decrypt : WGRunWitness (RxPacket × Option RxPacket)), ∃ out pid published ambient,
      pre = before ++ .rx (.consumed e.tag.occurrence e.tag.skb e.stamp receipt) ::
        (between ++ .rx (.buffered e) :: afterBuffer) ∧
      before = beforeDecrypt ++ .rx (.rx (.decrypt e.tag.skb decrypt)) :: afterDecrypt ∧
      e.origin = some receipt ∧ receipt.run.value = some e.tag.bytes ∧
      Published e.tag.skb decrypt out pid published ambient ∧
      ConsumeCertificate (Origins.HistorySupport.sessions (beforeDecrypt.filterMap RoutingJoint.rxEvent))
        e.tag.skb decrypt out pid published e.stamp receipt ∧
      ∃ v4 : Bool,
        ipTunnelParseProtocol e.tag.bytes = (if v4 then 4 else 6) ∧
        ipTunnelParseProtocol receipt.packet.bytes = (if v4 then 4 else 6) ∧
        PeerWinner (rootWidth v4) (sourceAddress v4 e.tag.bytes)
          (selectedFlat v4 (completionFold (before.filterMap RoutingJoint.routingEvent) ([],[])))
          (some receipt.peer) ∧
        sourceAddress v4 e.tag.bytes = sourceAddress v4 receipt.packet.bytes :=
  entered trace (parseTrace_shape json trace parsed) placeholders pre post e position

end Leanux.Proofs.WG.InitializedEntries
