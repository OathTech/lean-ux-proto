import Leanux.Proofs.WG.Index.RetirementReleaseSource
import Leanux.Proofs.WG.Index.HashSlotClearSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise
open Queues.RxCredits

/-- Retirement obligations transport along surviving hashed key rows. Removed
rows and removed peers create no obligation; retained peers preserve allocation
stamp and dead flag, while each retained key row preserves its embedded word. -/
theorem deadHashedReserved_transport (retired : Reservations) (d final : Device)
    (epoch : final.ifindex = d.ifindex)
    (table : ∀ entry ∈ final.indexTable, entry ∈ d.indexTable)
    (words : ∀ entry ∈ final.indexTable, ∀ kid, entry.owner = .keypair kid →
      ownerWord final entry.owner = ownerWord d entry.owner)
    (peers : ∀ (pid : PeerId) (p : Peer), final.peers[pid]? = some p →
      ∃ old : Peer, d.peers[pid]? = some old ∧
        old.internalId = p.internalId ∧ old.isDead = p.isDead)
    (reserved : DeadHashedReserved retired d) :
    DeadHashedReserved retired final := by
  intro entry member kid key pid p owner keyFound keyPeer peerFound dead
  obtain ⟨oldPeer,oldFound,stamp,oldDead⟩ := peers pid p peerFound
  have word : ownerWord d (.keypair kid) = some (some pid) := by
    have same := words entry member kid owner
    rw [owner] at same
    rw [← same]
    simp only [ownerWord,keyFound,Option.map_some,keyPeer]
  cases oldKeyFound : d.keypairs[kid]? with
  | none => simp [ownerWord,oldKeyFound] at word
  | some oldKey =>
    have oldKeyPeer : oldKey.peer = some pid := by
      simpa only [ownerWord,oldKeyFound,Option.map_some,Option.some.injEq] using word
    have member := reserved entry (table entry member) kid oldKey pid oldPeer owner
      oldKeyFound oldKeyPeer oldFound (oldDead.trans dead)
    rw [epoch,← stamp]
    exact member

/-- Updating an actual resident peer preserves retirement when allocation
identity and the dead flag are retained. Other fields may change freely. -/
theorem peerWrite_deadHashedReserved (retired : Reservations) (d : Device)
    (pid : PeerId) (p q : Peer) (resident : d.peers[pid]? = some p)
    (stamp : q.internalId = p.internalId) (dead : q.isDead = p.isDead)
    (reserved : DeadHashedReserved retired d) :
    DeadHashedReserved retired {d with peers := d.peers.insert pid q} := by
  apply deadHashedReserved_transport retired d {d with peers := d.peers.insert pid q} rfl (fun _ member => member)
    (fun _ _ _ owner => by simp only [owner,ownerWord]) _ reserved
  intro target peer found
  by_cases same : pid = target
  · subst target
    have equal : q = peer := by simpa using found
    subst peer
    exact ⟨p,resident,stamp.symm,dead.symm⟩
  · exact ⟨peer,by simpa [Std.TreeMap.getElem?_insert,same] using found,rfl,rfl⟩

/-- Both nonfinal decrement and final peer deletion retain every surviving
dead hashed owner's reservation. No empty-slot or detachment premise is needed
for this separate obligation. -/
theorem releasedPeer_deadHashedReserved (retired : Reservations) (d : Device)
    (pid : PeerId) (p : Peer) (resident : d.peers[pid]? = some p)
    (reserved : DeadHashedReserved retired d) :
    DeadHashedReserved retired (releasedPeerDevice d pid p) := by
  apply deadHashedReserved_transport retired d _ _ _ _ _ reserved
  · unfold releasedPeerDevice
    split <;> rfl
  · intro entry member
    rw [releasedPeer_table] at member
    split at member
    · exact (List.mem_filter.mp member).1
    · exact member
  · intro entry member kid owner
    simp only [owner,ownerWord,releasedPeer_keypairs]
  · intro target peer found
    by_cases same : pid = target
    · subst target
      rw [releasedPeer_peer] at found
      split at found
      · cases found
      · cases found
        exact ⟨p,resident,rfl,rfl⟩
    · rw [releasedPeer_other pid target d p same] at found
      exact ⟨peer,found,rfl,rfl⟩

/-- A normal key release's pure device effect retains the owner word of every
surviving hashed key row, including the decremented key on an ordinary nonfinal
put. Immediate unhash and last-reference erase impose no retained-row duty. -/
theorem releasedDevice_deadHashedReserved (retired : Reservations) (d : Device)
    (id : KeypairId) (k : Keypair) (now : Bool)
    (resident : d.keypairs[id]? = some k) (reserved : DeadHashedReserved retired d) :
    DeadHashedReserved retired (releasedDevice d id k now) := by
  have peers : (releasedDevice d id k now).peers = d.peers := by
    cases now <;> by_cases last : k.refcount = 1 <;>
      simp [releasedDevice,unhashKeypair,last]
  apply deadHashedReserved_transport retired d _ _ _ _ _ reserved
  · cases now <;> by_cases last : k.refcount = 1 <;>
      simp [releasedDevice,unhashKeypair,last]
  · intro entry member
    rw [released_table] at member
    split at member
    · exact (List.mem_filter.mp member).1
    · exact member
  · intro entry member kid owner
    by_cases same : id = kid
    · subst kid
      have notLast : k.refcount ≠ 1 := by
        intro last
        exact released_unhashed d id k now (.inr last) entry member owner
      simp only [owner,ownerWord,released_keypair,ite_eq_right notLast,
        Option.map_some,resident]
    · simp only [owner,ownerWord,released_other_keypair d id kid k now same]
  · intro pid p found
    rw [peers] at found
    exact ⟨p,found,rfl,rfl⟩

theorem clearPut_deadHashedReserved {retired : Reservations}
    {key : Option KeypairId} {d final : Device}
    (put : ClearPut key d final) (reserved : DeadHashedReserved retired d) :
    DeadHashedReserved retired final := by
  cases put with
  | null => exact reserved
  | present d id k resident live word =>
    exact releasedDevice_deadHashedReserved retired d id k true resident reserved

theorem clearStep_deadHashedReserved (retired : Reservations) (d : Device)
    (pid : PeerId) (slot : ClearSlot) (p : Peer) (final : Device)
    (resident : d.peers[pid]? = some p)
    (put : ClearPut (slot.read p) (clearWrite d pid slot p) final)
    (reserved : DeadHashedReserved retired d) : DeadHashedReserved retired final := by
  apply clearPut_deadHashedReserved put
  apply peerWrite_deadHashedReserved retired d pid p (slot.clear p) resident
  · cases slot <;> rfl
  · cases slot <;> rfl
  · exact reserved

/-- The ordered clear certificate carries retirement across aliased slot
releases without a static readiness or distinctness assumption. -/
theorem clearRun_deadHashedReserved {retired : Reservations}
    {pid : PeerId} {d final : Device} {slots : List ClearSlot}
    (steps : ClearRun pid d slots final) (reserved : DeadHashedReserved retired d) :
    DeadHashedReserved retired final := by
  induction steps with
  | nil => exact reserved
  | cons d slot p middle final rest resident put tail ih =>
    exact ih (clearStep_deadHashedReserved retired d pid slot p middle resident put reserved)

end Leanux.Proofs.WG.Index
