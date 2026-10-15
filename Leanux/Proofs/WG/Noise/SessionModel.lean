import Leanux.WG.Handshake
import Leanux.Proofs.WG.Noise.RotationModel
import Leanux.Proofs.WG.Index.AllocationModel
import Leanux.Proofs.WG.Index.TableModel

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

def sessionFirst (ck : List UInt8) : List UInt8 :=
  hmacBlake2s (hmacBlake2s ck []) [1]
def sessionSecond (ck : List UInt8) : List UInt8 :=
  hmacBlake2s (hmacBlake2s ck []) (sessionFirst ck ++ [2])

def sessionDerivedKey (k : Keypair) (initiator : Bool) (ck : List UInt8)
    (birth : Int64) : Keypair :=
  let first : SymmetricKey := { key := sessionFirst ck, birthdate := birth, isValid := true }
  let second : SymmetricKey := { key := sessionSecond ck, birthdate := birth, isValid := true }
  if initiator then { k with sending := first, receiving := second }
  else { k with receiving := first, sending := second }

def sessionZeroPeer (p : Peer) : Peer :=
  { p with
      ephemeralPrivate := List.replicate 32 0, remoteEphemeral := List.replicate 32 0,
      hash := List.replicate 32 0, chainingKey := List.replicate 32 0,
      remoteIndex := 0, handshakeState := 0 }

def sessionAssignedKey (k : Keypair) (p : Peer) (st : Nat) : Keypair :=
  { k with iAmTheInitiator := st == HANDSHAKE_CONSUMED_RESPONSE, remoteIndex := p.remoteIndex }

def sessionDerivedDevice (d : Device) (kp : KeypairId) (p : Peer) (k : Keypair)
    (st : Nat) (birth : Int64) : Device :=
  let assigned := { d with keypairs := d.keypairs.insert kp (sessionAssignedKey k p st) }
  { assigned with
    keypairs := assigned.keypairs.insert kp
      (sessionDerivedKey (sessionAssignedKey k p st) (st == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey birth) }

/-- Retain allocation, role assignment, derivation and zeroing as separate ordered
map writes, including overwriting a pre-existing allocation identity. -/
def sessionPrepared (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (birth : Int64) : Device :=
  let derived := sessionDerivedDevice (Index.createdDevice d counter p.handshakeEntryPeer)
    d.nextKeypairId p { internalId := counter + 1, peer := p.handshakeEntryPeer } p.handshakeState birth
  { derived with peers := derived.peers.insert pid (sessionZeroPeer p) }

/-- A normally returning successful session has these ordered effects. The
birthdate is existential here; no separate clock execution is postulated.
A rotation may erase an aliased allocation; final key residency is not asserted. -/
def SessionEffect (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (ok : Bool) (final : Device) (finalCounter : Nat) : Prop :=
  if ok then
    (p.handshakeState = HANDSHAKE_CREATED_RESPONSE ∨ p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE) ∧
    p.isDead = false ∧ p.handshakeEntryPeer ≠ none ∧ finalCounter = counter + 1 ∧
    ∃ birth rotated,
      RotationRun pid (sessionPrepared pid d p counter birth)
        (rotationPlan (sessionZeroPeer p) (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId) rotated ∧
      rotated.indexTable.any (·.owner == .handshake pid) = true ∧
      final = { rotated with indexTable := Index.replaceOwner pid d.nextKeypairId rotated.indexTable }
  else final = d ∧ finalCounter = counter

end Leanux.Proofs.WG.Noise
