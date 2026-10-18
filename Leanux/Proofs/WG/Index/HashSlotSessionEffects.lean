import Leanux.Proofs.WG.Index.HashSlotModel
import Leanux.Proofs.WG.Index.OwnerCoherenceSlotRemovalFrames
import Leanux.Proofs.WG.Index.SessionCoherenceFrames
import Leanux.Proofs.WG.Noise.RotationClaims
import Leanux.Proofs.WG.Noise.SessionSource
import Leanux.Proofs.WG.Index.SessionInvariantEffects
import Leanux.Proofs.WG.Index.SessionSequenceSource

import Leanux.Proofs.WG.Index.HashSlotRotationEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Allocation does not overwrite a hashed key below the initial cursor; derivation and handshake zeroing preserve every old covered slot. -/
theorem sessionPrepared_hashSlotCoverage (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (birth : Int64) (resident : d.peers[pid]? = some p)
    (bounded : KeypairOwnersBounded d) (covered : HashSlotCoverage d) :
    HashSlotCoverage (sessionPrepared pid d p counter birth) := by
  intro entry member kid owner
  obtain ⟨target,peer,key,found,keyFound,keyPeer,slot⟩ := covered entry member kid owner
  have different : d.nextKeypairId ≠ kid := (Nat.ne_of_lt (bounded entry member kid owner)).symm
  have stored : (sessionPrepared pid d p counter birth).keypairs[kid]? = some key := by
    simpa [sessionPrepared,sessionDerivedDevice,createdDevice,Std.TreeMap.getElem?_insert,different] using keyFound
  by_cases same : pid = target
  · subst target
    have equal : peer = p := Option.some.inj (found.symm.trans resident)
    subst peer
    exact ⟨pid,sessionZeroPeer p,key,by simp [sessionPrepared],stored,keyPeer,slot⟩
  · refine ⟨target,peer,key,?_,stored,keyPeer,slot⟩
    simpa [sessionPrepared,sessionDerivedDevice,createdDevice,Std.TreeMap.getElem?_insert,same] using found

theorem hashSlotCoverage_replace (d : Device) (pid : PeerId) (kid : KeypairId)
    (covered : HashSlotCoverage d)
    (installed : ∃ p key, d.peers[pid]? = some p ∧ d.keypairs[kid]? = some key ∧
      key.peer = some pid ∧ some kid ∈ clearKeys p) :
    HashSlotCoverage {d with indexTable := replaceOwner pid kid d.indexTable} := by
  intro entry member target owner
  obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
  by_cases replaced : old.owner == .handshake pid
  · simp only [replaced,↓reduceIte] at owner
    cases owner
    obtain ⟨p,key,peerStored,keyStored,keyPeer,slot⟩ := installed
    exact ⟨pid,p,key,peerStored,keyStored,keyPeer,slot⟩
  · simp only [replaced] at owner
    exact covered old oldMember target owner

/-- Successful publication derives self-ownership from the surviving handshake row. Initial allocation and rotation freshness protect the newly installed key; refusal retains the initial device. -/
theorem sessionEffect_hashSlotCoverage (pid : PeerId) (d : Device) (p : Peer)
    (counter finalCounter : Nat) (ok : Bool) (final : Device)
    (resident : d.peers[pid]? = some p) (bounded : KeypairOwnersBounded d)
    (fresh : SessionRotationFresh p d.nextKeypairId)
    (coherent : HashedOwnersCoherent d) (covered : HashSlotCoverage d)
    (effect : SessionEffect pid d p counter ok final finalCounter) :
    HashSlotCoverage final := by
  cases ok with
  | false =>
    obtain ⟨rfl,_⟩ := effect
    exact covered
  | true =>
    obtain ⟨state,alive,word,count,birth,rotated,steps,hashed,rfl⟩ := effect
    have prepared := sessionPrepared_hashSlotCoverage pid d p counter birth resident bounded covered
    have rotatedCoverage := rotationPlan_hashSlotCoverage pid _ rotated (sessionZeroPeer p)
      (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId
      (by simp [sessionPrepared]) prepared steps
    obtain ⟨entry,member,entryOwner⟩ := List.any_eq_true.mp hashed
    have own : entry.owner = .handshake pid := by simpa using entryOwner
    have entryEq : entry = {index := entry.index,owner := .handshake pid} := by
      cases entry
      simp_all
    have oldMember : {index := entry.index,owner := IndexOwner.handshake pid} ∈ d.indexTable := by
      apply (rotationRun_handshake_mem steps pid entry.index).mp
      simpa only [← entryEq] using member
    have self : p.handshakeEntryPeer = some pid := by
      obtain ⟨target,peer,oldWord,found,positive,identity⟩ := coherent _ oldMember
      change target = pid at identity
      subst target
      simpa [ownerWord,resident] using oldWord
    let key := sessionDerivedKey
      (sessionAssignedKey {internalId := counter + 1,peer := p.handshakeEntryPeer} p p.handshakeState)
      (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey birth
    have keyResident : rotated.keypairs[d.nextKeypairId]? = some key := by
      rw [rotationRun_excluded_key steps d.nextKeypairId fresh]
      simp [sessionPrepared,sessionDerivedDevice,createdDevice,key]
    have keyPeer : key.peer = some pid := by
      simp [key,sessionDerivedKey,sessionAssignedKey,self]
      split <;> rfl
    have caller := rotationRun_peer steps (sessionZeroPeer p)
      (by simp [sessionPrepared])
    have slot : some d.nextKeypairId ∈ clearKeys
        (rotationPeer (rotationPlan (sessionZeroPeer p)
          (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId) (sessionZeroPeer p)) := by
      by_cases role : p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE <;>
        by_cases pending : p.keypairNext.isSome = true <;>
        simp [rotationPlan,rotateWithNext,rotateWithoutNext,rotateResponder,
          rotationPeer,RotationWrite.apply,role,pending,sessionZeroPeer,clearKeys]
    exact hashSlotCoverage_replace rotated pid d.nextKeypairId rotatedCoverage
      ⟨_,key,caller,keyResident,keyPeer,slot⟩

end Leanux.Proofs.WG.Index
