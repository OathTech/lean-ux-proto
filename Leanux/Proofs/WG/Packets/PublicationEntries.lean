import Leanux.Proofs.WG.Queues.RxLinkPositions
import Leanux.Proofs.WG.Packets.PublicationChecks
import Leanux.Proofs.WG.Configuration.ConsumedRouting

/-! One selected Stack entry joins routing and configured publication evidence
through its actual earlier consume. All cuts are positions in the same joint
journal. These pure eliminators do not assume or assert runner preservation. -/
namespace Leanux.Proofs.WG.PublicationEntries
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues PublicationIdentity AllowedIps

/-- Reconstruct the strictly earlier publication occurrence in the full joint
prefix. The retained material/current-identity witness stays the same one. -/
theorem consumed_publication {h pre post : List RoutingJoint.Event}
    {occurrence id : Nat} {stamp : PacketStamp} {receipt : RxDisposition.ConsumeReceipt}
    (safe : PublicationChecks.Safe (h.filterMap RoutingJoint.rxEvent))
    (position : h = pre ++ .rx (.consumed occurrence id stamp receipt) :: post) :
    ∃ before after, ∃ (decrypt : WGRunWitness (RxPacket × Option RxPacket)),
      ∃ out pid published ambient,
      pre = before ++ .rx (.rx (.decrypt id decrypt)) :: after ∧
      Published id decrypt out pid published ambient ∧
      ConsumeCertificate (Origins.HistorySupport.sessions (before.filterMap RoutingJoint.rxEvent))
        id decrypt out pid published stamp receipt := by
  have checked := safe (pre.filterMap RoutingJoint.rxEvent)
    (.consumed occurrence id stamp receipt) (post.filterMap RoutingJoint.rxEvent)
    (by simp only [position,List.filterMap_append,List.filterMap_cons,RoutingJoint.rxEvent])
  obtain ⟨a,b,decrypt,out,pid,published,ambient,publicationPosition,source,certificate⟩ := checked
  obtain ⟨before,event,after,jointPosition,beforeEq,eventEq,_⟩ :=
    RxLink.filterMap_position RoutingJoint.rxEvent pre a (.rx (.decrypt id decrypt)) b publicationPosition
  cases event with
  | routing event => cases eventEq
  | rx event =>
    simp only [RoutingJoint.rxEvent,Option.some.injEq] at eventEq
    subst event
    exact ⟨before,after,decrypt,out,pid,published,ambient,jointPosition,source,beforeEq ▸ certificate⟩

/-- The selected entry follows its buffered event, actual successful consume
and earlier configured publication. The winning route uses the routing fold
at that same consume cut, independently of later mutations or a later Stop. -/
theorem entered_authorized {h pre post : List RoutingJoint.Event} {e : RxJoint.Entry}
    {initial : FlatTable × FlatTable}
    (linked : RxLink.HistoryLinked (h.filterMap RoutingJoint.rxEvent))
    (publication : PublicationChecks.Safe (h.filterMap RoutingJoint.rxEvent))
    (routing : RoutingPosition.Checks initial h)
    (position : h = pre ++ .rx (.entered e) :: post) :
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
          (selectedFlat v4 (completionFold (before.filterMap RoutingJoint.routingEvent) initial))
          (some receipt.peer) ∧
        sourceAddress v4 e.tag.bytes = sourceAddress v4 receipt.packet.bytes := by
  obtain ⟨receipt,before,between,afterBuffer,consumePosition,origin,value,source⟩ :=
    RxLink.entered_position linked position
  have consumed : h = before ++ .rx (.consumed e.tag.occurrence e.tag.skb e.stamp receipt) ::
      ((between ++ .rx (.buffered e) :: afterBuffer) ++ .rx (.entered e) :: post) := by
    simp only [position,consumePosition,List.append_assoc,List.cons_append]
  obtain ⟨beforeDecrypt,afterDecrypt,decrypt,out,pid,published,ambient,decryptPosition,
    actualPublication,certificate⟩ := consumed_publication publication consumed
  exact ⟨receipt,before,between,afterBuffer,beforeDecrypt,afterDecrypt,decrypt,out,pid,published,ambient,
    consumePosition,decryptPosition,origin,value,actualPublication,certificate,
    RoutingPosition.consume_authorized routing consumed source.1 e.tag.bytes value⟩

end Leanux.Proofs.WG.PublicationEntries
