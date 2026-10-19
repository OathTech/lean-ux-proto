import Leanux.Proofs.WG.Roaming.View
import Leanux.Proofs.WG.Origins.CurrentIdentity
import Leanux.Proofs.WG.Lifetimes.Tagged

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication
open Leanux Leanux.WG Lifetimes


/-- A reached endpoint-source check, before the data-consumption call. The
snapshots describe this check, not a completed setter or the run's final state. -/
structure Check where
  position : Nat
  occurrence : Nat
  skb : SkbId
  packetStamp : PacketStamp
  packet : RxPacket
  endpoint : Option Endpoint
  before : Campaign2.Snapshot
  after : Campaign2.Snapshot

/-- Historical authentication and same-session material evidence. The outer
packet source is carried with the ciphertext, not bound by the AEAD. -/
structure Authentication where
  decryptPosition : Nat
  decryptEntry : Campaign2.Snapshot
  ciphertext : RxPacket
  receivingKey : Keypair
  sessionEntry : Campaign2.Snapshot
  sessionAfter : Campaign2.Snapshot
  originalKey : Keypair
  context : SessionOrigin.Context

def Check.Facts (q : Check) : Prop :=
  q.endpoint = some (sourceEndpoint q.packet.source) ∧
  (q.packet.source.family = 4 ∨ q.packet.source.family = 6) ∧
  (q.before.wg.device.bind fun d => d.rxSkbs[q.skb]?) = some q.packet

def Authentication.Facts (e : Authentication) (q : Check) : Prop :=
  q.Facts ∧
  e.decryptPosition < q.position ∧
  (e.decryptEntry.wg.device.bind fun d => d.rxSkbs[q.skb]?) = some e.ciphertext ∧
  (e.decryptEntry.wg.device.bind fun d => d.keypairs[e.ciphertext.keypair]?) =
    some e.receivingKey ∧
  e.receivingKey.receiving.isValid = true ∧
  q.packet.peer = e.ciphertext.peer ∧
  q.packet = {e.ciphertext with nonce := u64le e.ciphertext.bytes 8, bytes := q.packet.bytes, state := .crypted} ∧
  aeadDecrypt e.receivingKey.receiving.key (counterNonce (u64le e.ciphertext.bytes 8))
    (e.ciphertext.bytes.drop 16) [] = some q.packet.bytes ∧
  e.context.slot = e.ciphertext.keypair ∧
  (∃ d, e.sessionEntry.wg.device = some d ∧
    d.peers[q.packet.peer]? = some e.context.peer ∧
    (e.context.peer.remoteStatic,q.packet.peer) ∈ d.peerHashtable) ∧
  e.context.peer.isDead = false ∧ e.context.word = some q.packet.peer ∧
  (e.sessionAfter.wg.device.bind fun d => d.keypairs[e.context.slot]?) =
    some e.originalKey ∧
  e.originalKey.receiving.isValid = true ∧ e.originalKey.peer = e.context.word ∧
  MaterialOrigin.material e.receivingKey = MaterialOrigin.material e.originalKey ∧
  (∀ p, q.before.peerAt q.packet.peer = some p →
    CurrentIdentity.identity p = CurrentIdentity.identity e.context.peer)

/-- The original indexed outcome paired with all reached projected checks. -/
structure Inspection where
  outcome : Except (Nat × Stop) Lean.Json
  checks : List Check


end Leanux.Proofs.WG.Roaming.PollAuthentication
