import Leanux.Proofs.WG.Roaming.ConsumedEndpointModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG
open Noise.ConfirmationOrder

/-- Projected data at the historical decrypt, supporting session and actual
consume entry. The plaintext's outer source is retained, not AEAD-bound. -/
structure ConsumptionAuthentication where
  decryptPosition : Nat
  decryptEntry : Campaign2.Snapshot
  ciphertext : RxPacket
  receivingKey : Keypair
  sessionEntry : Campaign2.Snapshot
  context : SessionOrigin.Context
  currentPeer : Peer

def ConsumptionAuthentication.Facts (e : ConsumptionAuthentication) (q : Record) : Prop :=
  e.decryptPosition < q.position ∧
  (e.decryptEntry.wg.device.bind fun d => d.rxSkbs[q.skb]?) = some e.ciphertext ∧
  (e.decryptEntry.wg.device.bind fun d => d.keypairs[e.ciphertext.keypair]?) = some e.receivingKey ∧
  e.receivingKey.receiving.isValid = true ∧
  q.observation.packet.peer = q.observation.peer ∧
  q.observation.packet = {e.ciphertext with
    nonce := u64le e.ciphertext.bytes 8, bytes := q.observation.packet.bytes, state := .crypted} ∧
  aeadDecrypt e.receivingKey.receiving.key (counterNonce (u64le e.ciphertext.bytes 8))
    (e.ciphertext.bytes.drop 16) [] = some q.observation.packet.bytes ∧
  q.observation.endpoint = sourceEndpoint q.observation.packet.source ∧
  (q.observation.packet.source.family = 4 ∨ q.observation.packet.source.family = 6) ∧
  remoteAt q.observation.before q.observation.peer =
    some (destination (sourceEndpoint q.observation.packet.source)) ∧
  q.observation.entry.peerAt q.observation.peer = some e.currentPeer ∧
  (∃ d, e.sessionEntry.wg.device = some d ∧
    d.peers[q.observation.peer]? = some e.context.peer ∧
    (e.context.peer.remoteStatic,q.observation.peer) ∈ d.peerHashtable) ∧
  e.context.peer.isDead = false ∧ e.context.word = some q.observation.peer ∧
  CurrentIdentity.identity e.currentPeer = CurrentIdentity.identity e.context.peer

end Leanux.Proofs.WG.Roaming
