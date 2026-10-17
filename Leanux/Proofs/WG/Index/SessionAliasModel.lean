import Leanux.Proofs.WG.Noise.SessionReadyModel
import Leanux.Proofs.WG.Index.OwnerCoherenceModel
import Leanux.Proofs.WG.Index.SessionCoherenceModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

namespace SessionAliasWitness

def peer : Peer := {
  remoteStatic := [], presharedKey := [], precomputedStaticStatic := [], internalId := 0,
  handshakeEntryPeer := some 0, handshakeState := HANDSHAKE_CREATED_RESPONSE,
  keypairPrevious := some 1 }
def entry : IndexEntry := {index := 7, owner := .handshake 0}
def published : IndexEntry := {index := 7, owner := .keypair 1}
def device : Device := {
  ifindex := 0, ifname := "wg0", numPeers := 1, peerList := [0],
  peers := ({} : Std.TreeMap PeerId Peer).insert 0 peer,
  indexTable := [entry], nextKeypairId := 1 }
def allocation : List UInt8 := 1 :: List.replicate 39 0
def clock : List UInt8 := List.replicate 8 0
def records : List HiddenRecord := sessionReadyRecords allocation clock []

def input (counter : Nat) (s : Campaign2.Snapshot) : Prop :=
  s.wg.device = some device ∧ s.wg.keypairCounter = counter ∧
  s.ambient.hidden = some records ∧ s.ambient.allocArmed.contains "kzallocKeypair" = true

end SessionAliasWitness
open SessionAliasWitness

/-- The dangling previous slot is outside all three tested local invariants.
No initialized reachability or slot-residency invariant is asserted. -/
theorem sessionAlias_entry : DeviceTablesSafe device ∧ HashedOwnersCoherent device ∧
    KeypairStoreBounded device := by
  refine ⟨?_, ?_, ?_⟩
  · simp [DeviceTablesSafe, UniqueIndices, UniqueOwners, KeypairOwnersBounded, device, entry]
  · intro e member
    have same : e = entry := by simpa [device] using member
    subst e
    refine ⟨0, peer, ?_, ?_, by decide, rfl⟩
    · simp [ownerWord, device, entry, peer]
    · simp [device]
  · simp [KeypairStoreBounded, device]


end Leanux.Proofs.WG.Index
