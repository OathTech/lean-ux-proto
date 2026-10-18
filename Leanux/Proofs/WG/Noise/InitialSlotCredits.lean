import Leanux.Proofs.WG.Noise.SessionReadyClaims
import Leanux.Proofs.WG.Queues.CurrentSlots

/-! Initial slot credits fund the actual rotation and the slots it retains.
Aliases consume one credit per occurrence. This is a local accounting
invariant, not an initialized-driver reachability claim. -/
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

theorem rotationReleases_slot_count (p : Peer) (initiator : Bool)
    (newKey id : KeypairId) :
    (rotationReleases (rotationPlan p initiator newKey)).count (some id) ≤
      (clearKeys p).count (some id) := by
  unfold rotationPlan
  split
  · split <;>
      simp only [rotateWithNext, rotateWithoutNext, rotationReleases, clearKeys,
        List.count_cons, List.count_nil] <;> omega
  · simp only [rotateResponder, rotationReleases, clearKeys,
      List.count_cons, List.count_nil]
    omega

theorem sessionReady_of_initial_slots (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (resident : d.peers[pid]? = some p)
    (slots : CurrentSlots.SlotInv (Affiliation.state d))
    (credits : ClearReady d (clearKeys p)) : SessionReady d p counter := by
  intro id occurs
  have bounded := rotationReleases_slot_count (sessionZeroPeer p)
    (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId id
  change (rotationReleases (rotationPlan (sessionZeroPeer p)
    (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId)).count (some id) ≤
      (clearKeys p).count (some id) at bounded
  have positive : 0 < (clearKeys p).count (some id) := Nat.lt_of_lt_of_le occurs bounded
  have member := List.count_pos_iff.mp positive
  have selected : p.keypairCurrent = some id ∨ p.keypairPrevious = some id ∨ p.keypairNext = some id := by
    simp only [clearKeys, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with next | previous | current
    · exact Or.inr (Or.inr next.symm)
    · exact Or.inr (Or.inl previous.symm)
    · exact Or.inl current.symm
  have old := slots pid (Affiliation.peerCell p) id
    (by simp [Affiliation.state, resident]) selected
  have distinct : d.nextKeypairId ≠ id := Nat.ne_of_gt old.1
  obtain ⟨key, found, word, funded⟩ := credits id positive
  refine ⟨key, ?_, word, Nat.le_trans bounded funded⟩
  simpa [Index.createdDevice, Std.TreeMap.getElem?_insert, distinct] using found

theorem rotationRun_reserve_credits {pid : PeerId} {d final : Device}
    {actions : List RotationAction} (run : RotationRun pid d actions final)
    (reserved : List (Option KeypairId))
    (credits : ClearReady d (rotationReleases actions ++ reserved)) :
    ClearReady final reserved := by
  induction run with
  | nil d => simpa [rotationReleases] using credits
  | write d final change p rest resident tail ih =>
    exact ih (rotationWrite_ready d pid change p _ credits)
  | put d middle final key rest release tail ih =>
    exact ih (clearPut_ready release (rotationReleases rest ++ reserved)
      (by simpa only [rotationReleases, List.cons_append] using credits))

theorem rotation_slot_account (p : Peer) (initiator : Bool)
    (newKey id : KeypairId) :
    (rotationReleases (rotationPlan p initiator newKey) ++
      clearKeys (rotationPeer (rotationPlan p initiator newKey) p)).count (some id) =
      (clearKeys p ++ [some newKey]).count (some id) := by
  cases initiator <;> cases next : p.keypairNext <;>
    simp [rotationPlan, next, rotateResponder, rotateWithNext, rotateWithoutNext,
      rotationReleases, rotationPeer, RotationWrite.apply, clearKeys,
      List.count_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem initial_slot_before_cursor (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (slots : CurrentSlots.SlotInv (Affiliation.state d))
    (id : KeypairId) (member : some id ∈ clearKeys p) : id < d.nextKeypairId := by
  have selected : p.keypairCurrent = some id ∨ p.keypairPrevious = some id ∨ p.keypairNext = some id := by
    simp only [clearKeys, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with next | previous | current
    · exact Or.inr (Or.inr next.symm)
    · exact Or.inr (Or.inl previous.symm)
    · exact Or.inl current.symm
  exact (slots pid (Affiliation.peerCell p) id
    (by simp [Affiliation.state, resident]) selected).1

theorem sessionPrepared_reserves (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (birth : Int64) (resident : d.peers[pid]? = some p)
    (slots : CurrentSlots.SlotInv (Affiliation.state d))
    (word : p.handshakeEntryPeer ≠ none) (credits : ClearReady d (clearKeys p)) :
    let actions := rotationPlan (sessionZeroPeer p)
      (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId
    ClearReady (sessionPrepared pid d p counter birth)
      (rotationReleases actions ++ clearKeys (rotationPeer actions (sessionZeroPeer p))) := by
  intro actions id occurs
  have account := rotation_slot_account (sessionZeroPeer p)
    (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId id
  change (rotationReleases actions ++ clearKeys (rotationPeer actions (sessionZeroPeer p))).count (some id) =
    (clearKeys p ++ [some d.nextKeypairId]).count (some id) at account
  by_cases same : id = d.nextKeypairId
  · subst id
    have absent : some d.nextKeypairId ∉ clearKeys p := by
      intro member
      exact Nat.lt_irrefl _ (initial_slot_before_cursor pid d p resident slots _ member)
    have count : (rotationReleases actions ++ clearKeys (rotationPeer actions (sessionZeroPeer p))).count
        (some d.nextKeypairId) = 1 := by
      rw [account]
      simp [List.count_eq_zero.mpr absent]
    refine ⟨sessionDerivedKey
      (sessionAssignedKey {internalId := counter + 1, peer := p.handshakeEntryPeer} p p.handshakeState)
      (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey birth, ?_, ?_, ?_⟩
    · simp [sessionPrepared, sessionDerivedDevice]
    · cases role : p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE <;>
        simpa [sessionDerivedKey, sessionAssignedKey, role] using word
    · cases role : p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE <;>
        simp [sessionDerivedKey, sessionAssignedKey, role, count]
  · have count : (rotationReleases actions ++ clearKeys (rotationPeer actions (sessionZeroPeer p))).count
        (some id) = (clearKeys p).count (some id) := by
      rw [account]
      simp [Ne.symm same]
    obtain ⟨key, found, owner, refs⟩ := credits id (by rwa [←count])
    refine ⟨key, ?_, owner, ?_⟩
    · simpa [sessionPrepared, sessionDerivedDevice, Index.createdDevice,
        Std.TreeMap.getElem?_insert, same, Ne.symm same] using found
    · rwa [count]

theorem sessionEffect_preserves_slot_credits (pid : PeerId) (d final : Device)
    (p : Peer) (counter finalCounter : Nat) (resident : d.peers[pid]? = some p)
    (slots : CurrentSlots.SlotInv (Affiliation.state d))
    (credits : ClearReady d (clearKeys p))
    (effect : SessionEffect pid d p counter true final finalCounter) :
    ∃ after, final.peers[pid]? = some after ∧ ClearReady final (clearKeys after) := by
  obtain ⟨_, _, word, _, birth, rotated, run, _, rfl⟩ := effect
  let actions := rotationPlan (sessionZeroPeer p)
    (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId
  let after := rotationPeer actions (sessionZeroPeer p)
  have funded := rotationRun_reserve_credits run (clearKeys after)
    (sessionPrepared_reserves pid d p counter birth resident slots word credits)
  refine ⟨after, ?_, funded⟩
  exact rotationRun_peer run (sessionZeroPeer p) (by simp [sessionPrepared])

end Leanux.Proofs.WG.Noise
