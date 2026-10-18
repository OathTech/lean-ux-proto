import Leanux.Proofs.WG.Roaming.ConsumptionAuthenticationModel
import Leanux.Proofs.WG.Roaming.ConsumedEndpointHistorySource

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes Noise.ConsumeConfirmation Noise.ConfirmationOrder

/-- Native witnesses are hidden behind the campaign projection. The decrypt
position is strictly before this exact completed consume; its supporting
session is in that decrypt's strict earlier prefix. -/
def ConsumptionAuthentication.Valid (trace : Runner.Trace) (placeholders : Bool)
    (q : Record) (e : ConsumptionAuthentication) : Prop :=
  ∃ (pre post before after : List RxHistory.Event)
    (r : RxDisposition.ConsumeReceipt)
    (decrypt : WGRunWitness (RxPacket × Option RxPacket))
    (out : RxPacket) (pid : PeerId) (published : WGWorld) (ambient : Ambient)
    (material : WGRunWitness (Option SessionOrigin.Context)),
    history trace placeholders = pre ++ .consumed q.occurrence q.skb q.packetStamp r :: post ∧
    q.position = pre.length ∧ Matches q.position q.occurrence q.skb q.packetStamp r q ∧
    pre = before ++ .rx (.decrypt q.skb decrypt) :: after ∧
    PublicationIdentity.Published q.skb decrypt out pid published ambient ∧
    PublicationIdentity.ConsumeCertificate (Origins.HistorySupport.sessions before)
      q.skb decrypt out pid published q.packetStamp r ∧
    SessionOrigin.Receipt.material r.peer material ∈ Origins.HistorySupport.sessions before ∧
    material.Valid (SessionOrigin.front r.peer) ∧ material.value = some e.context ∧
    ConfiguredSession.Configured r.peer material.before e.context ∧
    e.decryptPosition = before.length ∧
    e.decryptEntry = Campaign2.snapshot decrypt.before decrypt.ambientBefore ∧
    e.ciphertext = decrypt.value.1 ∧
    (decrypt.before.dev.bind fun d => d.keypairs[decrypt.value.1.keypair]?) = some e.receivingKey ∧
    e.sessionEntry = Campaign2.snapshot material.before material.ambientBefore ∧
    q.observation.entry.peerAt q.observation.peer = some e.currentPeer ∧
    CurrentIdentity.identity e.currentPeer = CurrentIdentity.identity e.context.peer


end Leanux.Proofs.WG.Roaming
