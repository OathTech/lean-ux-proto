import Leanux.Proofs.WG.Index.RetirementRetentionEffects
import Leanux.Proofs.WG.Index.HashSlotSessionEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Queues.RxCredits

/-- Actual rotation writes preserve allocation identity/deadness; immediate
puts remove obligations but create no new dead hashed owner. -/
theorem rotationRun_deadHashedReserved {retired : Reservations}
    {pid : PeerId} {d final : Device} {actions : List RotationAction}
    (steps : RotationRun pid d actions final) (reserved : DeadHashedReserved retired d) :
    DeadHashedReserved retired final := by
  induction steps with
  | nil => exact reserved
  | write d final change p rest resident tail ih =>
    apply ih
    apply peerWrite_deadHashedReserved retired d pid p (change.apply p) resident
    · cases change <;> rfl
    · cases change <;> rfl
    · exact reserved
  | put d middle final key rest release tail ih =>
    exact ih (clearPut_deadHashedReserved release reserved)

/-- Handshake zeroing retains retirement identity. Allocation/derivation do
not overwrite any old hashed key below the supplied cursor bound. -/
theorem sessionPrepared_deadHashedReserved (retired : Reservations)
    (pid : PeerId) (d : Device) (p : Peer) (counter : Nat) (birth : Int64)
    (resident : d.peers[pid]? = some p) (bounded : KeypairOwnersBounded d)
    (reserved : DeadHashedReserved retired d) :
    DeadHashedReserved retired (sessionPrepared pid d p counter birth) := by
  let derived := sessionDerivedDevice (createdDevice d counter p.handshakeEntryPeer)
    d.nextKeypairId p {internalId := counter + 1,peer := p.handshakeEntryPeer}
      p.handshakeState birth
  have beforeZero : DeadHashedReserved retired derived := by
    apply deadHashedReserved_transport retired d derived rfl (fun _ member => member) ?_
      (fun target peer found => ⟨peer,found,rfl,rfl⟩) reserved
    intro entry member kid owner
    have different : d.nextKeypairId ≠ kid := (Nat.ne_of_lt (bounded entry member kid owner)).symm
    simp only [owner,ownerWord]
    simp [derived,sessionDerivedDevice,createdDevice,Std.TreeMap.getElem?_insert,different]
  exact peerWrite_deadHashedReserved retired derived pid p (sessionZeroPeer p)
    resident rfl rfl beforeZero

/-- The ordered slot-update program never changes the peer's dead flag. -/
theorem rotationPeer_isDead (actions : List RotationAction) (p : Peer) :
    (rotationPeer actions p).isDead = p.isDead := by
  induction actions generalizing p with
  | nil => rfl
  | cons action rest ih =>
    cases action with
    | put key => exact ih p
    | write change =>
      rw [rotationPeer,ih]
      cases change <;> rfl

/-- Publishing a key owned by the actual live caller introduces no dead-owner
retirement duty. All other hashed rows retain their existing duties. -/
theorem deadHashedReserved_replace_live (retired : Reservations) (d : Device)
    (pid : PeerId) (kid : KeypairId) (p : Peer) (key : Keypair)
    (resident : d.peers[pid]? = some p) (keyResident : d.keypairs[kid]? = some key)
    (keyPeer : key.peer = some pid) (live : p.isDead = false)
    (reserved : DeadHashedReserved retired d) :
    DeadHashedReserved retired {d with indexTable := replaceOwner pid kid d.indexTable} := by
  intro entry member target actual owner peer indexOwner found actualPeer peerFound dead
  obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
  by_cases replaced : old.owner == .handshake pid
  · simp only [replaced,↓reduceIte] at indexOwner
    cases indexOwner
    have sameKey : actual = key := Option.some.inj (found.symm.trans keyResident)
    subst actual
    have sameOwner : owner = pid := Option.some.inj (actualPeer.symm.trans keyPeer)
    subst owner
    have samePeer : peer = p := Option.some.inj (peerFound.symm.trans resident)
    subst peer
    rw [live] at dead
    cases dead
  · simp only [replaced] at indexOwner
    exact reserved old oldMember target actual owner peer indexOwner found actualPeer peerFound dead

/-- True session completion supplies the actual nondead guard. Its surviving
handshake row and initial coherence identify the new key's caller; no extra
live-caller or stamped-retirement entry premise is used. False retains Device. -/
theorem sessionEffect_deadHashedReserved (retired : Reservations)
    (pid : PeerId) (d : Device) (p : Peer) (counter finalCounter : Nat)
    (ok : Bool) (final : Device) (resident : d.peers[pid]? = some p)
    (bounded : KeypairOwnersBounded d) (fresh : SessionRotationFresh p d.nextKeypairId)
    (coherent : HashedOwnersCoherent d) (reserved : DeadHashedReserved retired d)
    (effect : SessionEffect pid d p counter ok final finalCounter) :
    DeadHashedReserved retired final := by
  cases ok with
  | false =>
    obtain ⟨rfl,_⟩ := effect
    exact reserved
  | true =>
    obtain ⟨state,alive,word,count,birth,rotated,steps,hashed,rfl⟩ := effect
    have rotatedReserved := rotationRun_deadHashedReserved steps
      (sessionPrepared_deadHashedReserved retired pid d p counter birth resident bounded reserved)
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
    exact deadHashedReserved_replace_live retired rotated pid d.nextKeypairId _ key
      caller keyResident keyPeer (by rw [rotationPeer_isDead]; exact alive) rotatedReserved
end Leanux.Proofs.WG.Index
