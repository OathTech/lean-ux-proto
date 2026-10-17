import Leanux.Proofs.WG.Noise.SessionModel
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

structure SessionClockInput where
  keypair : KeypairId
  initiator : Bool
  chainingKey : List UInt8

def sessionClockAssigned (d : Device) (p : Peer) (counter : Nat) : Device :=
  let allocated := Index.createdDevice d counter p.handshakeEntryPeer
  {allocated with keypairs := (allocated.keypairs.insert d.nextKeypairId
    (sessionAssignedKey {internalId := counter + 1, peer := p.handshakeEntryPeer}
      p p.handshakeState))}

/-- The successful ordered session effect with its birthdate fixed to the
actual derivation read. Aliased puts may still erase the allocated key. -/
def SessionBirthEffect (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (birth : Int64) (final : Device) (finalCounter : Nat) : Prop :=
  (p.handshakeState = HANDSHAKE_CREATED_RESPONSE ∨ p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE) ∧
  p.isDead = false ∧ p.handshakeEntryPeer ≠ none ∧ finalCounter = counter + 1 ∧
  ∃ rotated,
    RotationRun pid (sessionPrepared pid d p counter birth)
      (rotationPlan (sessionZeroPeer p) (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId) rotated ∧
    rotated.indexTable.any (·.owner == .handshake pid) = true ∧
    final = {rotated with indexTable := Index.replaceOwner pid d.nextKeypairId rotated.indexTable}

structure SessionClockReceipt where
  input : SessionClockInput
  before : Campaign2.Product.Snapshot
  birth : Int64
  after : Campaign2.Product.Snapshot

def SessionClockObservation (pid : PeerId) (entry : Campaign2.Product.Snapshot)
    (receipt : Campaign2.Product.Outcome (Option SessionClockReceipt)) (ok : Bool)
    (final : Campaign2.Product.Snapshot) : Prop :=
  ∃ d p, entry.wg.device = some d ∧ d.peers[pid]? = some p ∧
    if ok then ∃ seen out,
      receipt = .ok (some seen, seen.after) ∧
      seen.input = ⟨d.nextKeypairId, p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE, p.chainingKey⟩ ∧
      seen.before.wg.device = some (sessionClockAssigned d p entry.wg.keypairCounter) ∧
      seen.after.wg = seen.before.wg ∧ final.wg.device = some out ∧
      SessionBirthEffect pid d p entry.wg.keypairCounter seen.birth out final.wg.keypairCounter
    else receipt = .ok (none, final) ∧ final.wg.device = entry.wg.device ∧
      final.wg.keypairCounter = entry.wg.keypairCounter
end Leanux.Proofs.WG.Noise
