import Leanux.Proofs.WG.Index.OwnerCoherenceSessionFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceTableEffects

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- The actual successful session effect supplies a surviving old handshake
row. Initial coherence determines its self peer word; freshness retains the
new owner through rotation until publication. False returns keep the device. -/
theorem sessionEffect_owner_coherent (pid : PeerId) (d : Device) (p : Peer)
    (counter finalCounter : Nat) (ok : Bool) (final : Device)
    (resident : d.peers[pid]? = some p) (bounded : KeypairOwnersBounded d)
    (fresh : SessionRotationFresh p d.nextKeypairId)
    (coherent : HashedOwnersCoherent d)
    (effect : SessionEffect pid d p counter ok final finalCounter) :
    HashedOwnersCoherent final := by
  cases ok with
  | false =>
    obtain ⟨rfl, _⟩ := effect
    exact coherent
  | true =>
    obtain ⟨state, alive, word, count, birth, rotated, steps, hashed, rfl⟩ := effect
    have rotatedCoherent := rotationRun_owner_coherent steps
      (sessionPrepared_owner_coherent pid d p counter birth resident bounded coherent)
    obtain ⟨entry, member, entryOwner⟩ := List.any_eq_true.mp hashed
    have own : entry.owner = .handshake pid := by simpa using entryOwner
    have entryEq : entry = {index := entry.index, owner := .handshake pid} := by
      cases entry
      simp_all
    have oldMember : {index := entry.index, owner := IndexOwner.handshake pid} ∈ d.indexTable := by
      apply (rotationRun_handshake_mem steps pid entry.index).mp
      simpa only [← entryEq] using member
    have self : p.handshakeEntryPeer = some pid := by
      obtain ⟨target, peer, oldWord, found, positive, identity⟩ := coherent _ oldMember
      change target = pid at identity
      subst target
      simpa [ownerWord, resident] using oldWord
    let key := sessionDerivedKey
      (sessionAssignedKey {internalId := counter + 1, peer := p.handshakeEntryPeer} p p.handshakeState)
      (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey birth
    have excluded : some d.nextKeypairId ∉ rotationReleases
        (rotationPlan (sessionZeroPeer p) (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId) := by
      exact fresh
    have keyResident : rotated.keypairs[d.nextKeypairId]? = some key := by
      rw [rotationRun_excluded_key steps d.nextKeypairId excluded]
      simp [sessionPrepared, sessionDerivedDevice, createdDevice, key]
    have keyPeer : key.peer = some pid := by
      simp [key, sessionDerivedKey, sessionAssignedKey, self]
      split <;> rfl
    have keyCount : key.refcount = 1 := by
      simp [key, sessionDerivedKey, sessionAssignedKey]
      split <;> rfl
    apply hashedOwnersCoherent_replace rotated pid d.nextKeypairId rotatedCoherent
    obtain ⟨target, peer, targetWord, found, positive, identity⟩ := rotatedCoherent entry member
    have same : target = pid := by simpa only [own] using identity
    subst target
    exact ⟨pid, peer, by simp [ownerWord, keyResident, keyPeer], found, positive,
      key, keyResident, by rw [keyCount]; decide⟩

end Leanux.Proofs.WG.Index
