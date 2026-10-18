import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationSource
import Leanux.Proofs.WG.Packets.PublicationRunner

/-! Reuse campaign 1's actual initialized receive journal. Its completed
consumer events include normal nondelivery and precede any later failed work;
the separate inner observer is still needed if this consumer itself Stops. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Confirmation
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues Lifetimes MaterialOrigin

def SourceCut (r : RxDisposition.ConsumeReceipt) (c : WGRunWitness Bool) : Prop :=
  ((setPeerEndpoint r.peer r.endpoint).run r.run.before).run r.run.ambientBefore =
    .ok (((), c.before), c.ambientBefore) ∧
  c.Valid (receivedWithKeypair r.peer r.packet.keypair) ∧
  ((afterConfirmation r.peer r.packet c.value).run c.after).run c.ambientAfter =
    .ok ((r.run.value, r.run.after), r.run.ambientAfter)

theorem completed_source_cut (r : RxDisposition.ConsumeReceipt) (valid : r.Valid) :
    ∃ c, SourceCut r c := by
  have run := valid
  change ((consumeDataDone r.peer r.packet r.endpoint).run r.run.before).run r.run.ambientBefore =
    .ok ((r.run.value, r.run.after), r.run.ambientAfter) at run
  rw [source, bind_ok_ambient] at run
  obtain ⟨value, middle, a, endpoint, rest⟩ := run
  cases value
  rw [bind_ok_ambient] at rest
  obtain ⟨confirmed, next, b, confirm, suffix⟩ := rest
  exact ⟨⟨confirmed, middle, next, a, b⟩, endpoint, confirm, suffix⟩

/-- A local form with all historical and native connections exposed. -/
def AuthenticatedSource (pre : List RxHistory.Event) (id : SkbId)
    (r : RxDisposition.ConsumeReceipt) : Prop :=
  ∃ before after, ∃ (decrypt : WGRunWitness (RxPacket × Option RxPacket)), ∃ out d k c,
    pre = before ++ .rx (.decrypt id decrypt) :: after ∧
    decrypt.Valid (RxOrigin.readDecrypt id) ∧ decrypt.value.2 = some out ∧
    decrypt.before.dev = some d ∧ d.keypairs[decrypt.value.1.keypair]? = some k ∧
    r.packet = {out with state := .crypted} ∧
    r.packet.keypair = decrypt.value.1.keypair ∧
    r.packet.nonce = u64le decrypt.value.1.bytes 8 ∧
    aeadDecrypt k.receiving.key (counterNonce (u64le decrypt.value.1.bytes 8))
      (decrypt.value.1.bytes.drop 16) [] = some r.packet.bytes ∧
    SourceCut r c

theorem initialized_authenticated (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (occurrence : Nat) (id : SkbId) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .consumed occurrence id stamp r :: post) :
    AuthenticatedSource pre id r := by
  obtain ⟨before, after, decrypt, out, publishedPeer, published, ambient,
    history, publication, certificate⟩ :=
    PublicationRunner.consumed trace placeholders pre post occurrence id stamp r position
  obtain ⟨d, k, device, _, key, _, _, shape, aead⟩ :=
    RxOrigin.decrypt_receipt id decrypt out publication.1 publication.2.1
  obtain ⟨c, cut⟩ := completed_source_cut r certificate.1.1
  have packet := certificate.2.2.1
  refine ⟨before, after, decrypt, out, d, k, c, history, publication.1, publication.2.1,
    device, key, packet, ?_, ?_, ?_, cut⟩
  · rw [packet, shape]
  · rw [packet, shape]
  · simpa only [packet] using aead

end Leanux.Proofs.WG.HandshakeSecurity.Confirmation
