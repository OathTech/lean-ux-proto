import Leanux.Proofs.WG.Index.OwnerCoherenceSlotRemovalModel
import Leanux.Proofs.WG.Index.OwnerCoherenceQuietRemovalFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceClearFrames
import Leanux.Proofs.WG.Config.LiveRemovalModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- A normal immediate keypair release removes its owner and leaves every
surviving owner's stored word intact. This includes non-final releases. -/
theorem clearPut_retained_owner {key : Option KeypairId} {d final : Device}
    (put : ClearPut key d final) (e : IndexEntry) (member : e ∈ final.indexTable) :
    e ∈ d.indexTable ∧ ownerWord final e.owner = ownerWord d e.owner ∧
      ∀ id, key = some id → e.owner ≠ .keypair id := by
  cases put with
  | null d => exact ⟨member,rfl,by intro id impossible; cases impossible⟩
  | present d id k resident live word =>
    have table := released_table d id k true
    have old : e ∈ d.indexTable ∧ e.owner ≠ .keypair id := by
      simpa [table, removeOwner] using member
    refine ⟨old.1,?_,?_⟩
    · cases owner : e.owner with
      | handshake own =>
        by_cases last : k.refcount = 1 <;> simp [ownerWord, releasedDevice, unhashKeypair, last]
      | keypair own =>
        have different : id ≠ own := by intro same; subst own; exact old.2 owner
        simp only [ownerWord, released_other_keypair d id own k true different]
    · intro other same
      cases same
      exact old.2

/-- A slot-clear step preserves its remaining owners' words, removes the
selected key owner and writes only the selected slot of the resident peer. -/
theorem clearStep_retained_owner (d : Device) (pid : PeerId) (slot : ClearSlot)
    (p : Peer) (final : Device) (resident : d.peers[pid]? = some p)
    (put : ClearPut (slot.read p) (clearWrite d pid slot p) final)
    (e : IndexEntry) (member : e ∈ final.indexTable) :
    e ∈ d.indexTable ∧ ownerWord final e.owner = ownerWord d e.owner ∧
      (∀ id, slot.read p = some id → e.owner ≠ .keypair id) ∧
      final.peers[pid]? = some (slot.clear p) := by
  obtain ⟨old,word,unhashed⟩ := clearPut_retained_owner put e member
  refine ⟨old,word.trans ?_,unhashed,?_⟩
  · cases owner : e.owner with
    | keypair id => rfl
    | handshake own =>
      by_cases same : pid = own
      · subst own
        cases slot <;> simp [ownerWord, clearWrite, ClearSlot.clear, resident]
      · simp [ownerWord, clearWrite, Std.TreeMap.getElem?_insert, same]
  · rw [clearPut_peers put]
    simp [clearWrite]

/-- Actual next/previous/current clearing discharges the covered owners before
the peer's final release. Repeated key identities need no static budget here:
the ClearRun certificate itself comes only from a normal execution. -/
theorem clearRun_covered_detached (pid : PeerId) (d final : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (steps : ClearRun pid d [.next,.previous,.current] final)
    (covered : LastOwnerCovered d pid p) :
    LastOwnerDetached final pid (Config.emptyKeysPeer p) := by
  cases steps with
  | cons d slot p1 middle1 final rest resident1 put1 tail1 =>
    have same : p1 = p := Option.some.inj (resident1.symm.trans resident)
    subst p1
    cases tail1 with
    | cons middle1 slot2 p2 middle2 final rest2 resident2 put2 tail2 =>
      have peer1 : middle1.peers[pid]? = some (ClearSlot.next.clear p) := by
        rw [clearPut_peers put1]
        simp [clearWrite]
      have same : p2 = ClearSlot.next.clear p := Option.some.inj (resident2.symm.trans peer1)
      subst p2
      cases tail2 with
      | cons middle2 slot3 p3 middle3 final rest3 resident3 put3 tail3 =>
        have peer2 : middle2.peers[pid]? = some (ClearSlot.previous.clear (ClearSlot.next.clear p)) := by
          rw [clearPut_peers put2]
          simp [clearWrite]
        have same : p3 = ClearSlot.previous.clear (ClearSlot.next.clear p) :=
          Option.some.inj (resident3.symm.trans peer2)
        subst p3
        cases tail3
        intro last e member kept word
        obtain ⟨member2,word3,absent3,_⟩ :=
          clearStep_retained_owner middle2 pid .current _ _ resident3 put3 e member
        obtain ⟨member1,word2,absent2,_⟩ :=
          clearStep_retained_owner middle1 pid .previous _ middle2 resident2 put2 e member2
        obtain ⟨member0,word1,absent1,_⟩ :=
          clearStep_retained_owner d pid .next p middle1 resident1 put1 e member1
        have oldWord : ownerWord d e.owner = some (some pid) := by
          rw [← word1, ← word2, ← word3]
          exact word
        obtain own | ⟨id,owner,listed⟩ := covered last e member0 oldWord
        · exact kept own
        · simp only [clearKeys, List.mem_cons, List.not_mem_nil, or_false] at listed
          rcases listed with next | previous | current
          · exact absent1 id next.symm owner
          · exact absent2 id previous.symm owner
          · exact absent3 id current.symm owner

/-- Timer deletion changes neither owner words nor reference counts. -/
theorem deleteTimers_owner_conditions (ts : List PeerTimer) (d : Device)
    (pid : PeerId) (p : Peer) (resident : d.peers[pid]? = some p)
    (coherent : HashedOwnersCoherent d) (detached : LastOwnerDetached d pid p) :
    HashedOwnersCoherent (Config.deleteTimersDevice ts d pid p) ∧
      LastOwnerDetached (Config.deleteTimersDevice ts d pid p) pid
        (Config.deleteTimersPeer ts p) := by
  induction ts generalizing d p with
  | nil => exact ⟨coherent,detached⟩
  | cons t ts ih =>
    apply ih (Config.withPeer d pid ((p.setTimer t none).setWheel t none))
      ((p.setTimer t none).setWheel t none) (by simp [Config.withPeer])
    · exact peerWrite_owner_coherent d pid p _ resident (by cases t <;> rfl)
        (by cases t <;> rfl) coherent
    · exact peerWrite_lastOwnerDetached d pid p _ (by cases t <;> rfl) detached

/-- A normal covered clear followed by timer cleanup and peer release retains
owner coherence. Reference failure remains outside the normal ClearRun domain. -/
theorem removedAfterClear_owner_coherent (pid : PeerId) (d cleared : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (coherent : HashedOwnersCoherent d) (covered : LastOwnerCovered d pid p)
    (steps : ClearRun pid d [.next,.previous,.current] cleared)
    (found : cleared.peers[pid]? = some (Config.emptyKeysPeer p)) :
    HashedOwnersCoherent (Config.removedAfterClear cleared pid p) := by
  have detached := clearRun_covered_detached pid d cleared p resident steps covered
  have safe := clearRun_owner_coherent steps coherent
  obtain ⟨safe,detached⟩ := deleteTimers_owner_conditions PeerTimer.all cleared pid
    (Config.emptyKeysPeer p) found safe detached
  generalize cleanedEq : Config.deleteTimersDevice PeerTimer.all cleared pid
    (Config.emptyKeysPeer p) = cleaned at safe detached ⊢
  generalize peerEq : Config.deleteTimersPeer PeerTimer.all (Config.emptyKeysPeer p) = released
    at detached ⊢
  have refcount : released.refcount = p.refcount := by
    rw [← peerEq]
    exact Config.quietCleanup_refcount p
  have present : cleaned.peers[pid]? = some released := by
    rw [← cleanedEq, ← peerEq]
    exact Config.deleteTimers_resident _ _ _ _ found
  unfold Config.removedAfterClear
  change HashedOwnersCoherent (releasedPeerDevice
    {Config.deleteTimersDevice PeerTimer.all cleared pid (Config.emptyKeysPeer p) with
      numPeers := (Config.deleteTimersDevice PeerTimer.all cleared pid (Config.emptyKeysPeer p)).numPeers - 1}
    pid (Config.deleteTimersPeer PeerTimer.all (Config.emptyKeysPeer p)))
  rw [cleanedEq,peerEq]
  by_cases last : released.refcount = 1
  · exact (lastPeerRelease_coherent_iff {cleaned with numPeers := cleaned.numPeers - 1}
      pid released last safe).mpr (detached last)
  · exact nonlastPeerRelease_coherent {cleaned with numPeers := cleaned.numPeers - 1}
      pid released present (by rw [refcount] at last ⊢; omega) safe

/-- A peer write preserves the entry coverage obligation when it retains its
reference count and slot choices. Its own handshake is covered independently. -/
theorem peerWrite_lastOwnerCovered (d : Device) (pid : PeerId) (p q : Peer)
    (count : q.refcount = p.refcount) (keys : clearKeys q = clearKeys p)
    (covered : LastOwnerCovered d pid p) :
    LastOwnerCovered {d with peers := d.peers.insert pid q} pid q := by
  intro last e member word
  by_cases own : e.owner = .handshake pid
  · exact Or.inl own
  · have oldWord : ownerWord d e.owner = some (some pid) := by
      cases owner : e.owner with
      | keypair id => simpa only [owner,ownerWord] using word
      | handshake other =>
        have different : pid ≠ other := by intro same; subst other; exact own owner
        simpa [owner,ownerWord,Std.TreeMap.getElem?_insert,different] using word
    rcases covered (count ▸ last) e member oldWord with hand | ⟨id,owner,slot⟩
    · exact Or.inl hand
    · exact Or.inr ⟨id,owner,keys ▸ slot⟩

end Leanux.Proofs.WG.Index
