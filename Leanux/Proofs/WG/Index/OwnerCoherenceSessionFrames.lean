import Leanux.Proofs.WG.Index.OwnerCoherenceKeypairReleaseFrames
import Leanux.Proofs.WG.Index.SessionCoherenceFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Replacing the actual resident peer while retaining its embedded owner word
and reference count preserves every hashed owner's coherence. -/
theorem peerWrite_owner_coherent (d : Device) (pid : PeerId) (p q : Peer)
    (resident : d.peers[pid]? = some p)
    (word : q.handshakeEntryPeer = p.handshakeEntryPeer)
    (count : q.refcount = p.refcount) (coherent : HashedOwnersCoherent d) :
    HashedOwnersCoherent {d with peers := d.peers.insert pid q} := by
  have ownerWordSame (owner : IndexOwner) :
      ownerWord {d with peers := d.peers.insert pid q} owner = ownerWord d owner := by
    cases owner with
    | keypair id => rfl
    | handshake own =>
      by_cases same : pid = own
      · subst own
        simp [ownerWord, resident, word]
      · simp [ownerWord, Std.TreeMap.getElem?_insert, same]
  intro e member
  obtain ⟨target, peer, oldWord, found, positive, owned⟩ := coherent e member
  by_cases same : pid = target
  · subst target
    have equal : peer = p := Option.some.inj (found.symm.trans resident)
    subst peer
    refine ⟨pid, q, ?_, by simp, ?_, ?_⟩
    · rw [ownerWordSame]
      exact oldWord
    · rw [count]
      exact positive
    · cases ownerEq : e.owner <;> simpa only [ownerEq] using owned
  · refine ⟨target, peer, ?_, ?_, positive, ?_⟩
    · rw [ownerWordSame]
      exact oldWord
    · simpa [Std.TreeMap.getElem?_insert, same] using found
    · cases ownerEq : e.owner <;> simpa only [ownerEq] using owned

/-- Allocation and key derivation touch no initially hashed keypair owner when
its identity is below the cursor; handshake zeroing retains owner metadata. -/
theorem sessionPrepared_owner_coherent (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (birth : Int64) (resident : d.peers[pid]? = some p)
    (bounded : KeypairOwnersBounded d) (coherent : HashedOwnersCoherent d) :
    HashedOwnersCoherent (sessionPrepared pid d p counter birth) := by
  let derived := sessionDerivedDevice (createdDevice d counter p.handshakeEntryPeer)
    d.nextKeypairId p {internalId := counter + 1, peer := p.handshakeEntryPeer}
    p.handshakeState birth
  have unchangedPeers : derived.peers = d.peers := rfl
  have prepared : HashedOwnersCoherent derived := by
    intro e member
    have old := coherent e member
    cases owner : e.owner with
    | handshake own =>
      simpa only [OwnerCoherent, owner, ownerWord, unchangedPeers] using old
    | keypair id =>
      have different : d.nextKeypairId ≠ id := (Nat.ne_of_lt (bounded e member id owner)).symm
      simpa [derived, OwnerCoherent, owner, ownerWord, sessionDerivedDevice,
        createdDevice, Std.TreeMap.getElem?_insert, different] using old
  exact peerWrite_owner_coherent derived pid p (sessionZeroPeer p)
    (by rw [unchangedPeers]; exact resident) rfl rfl prepared

/-- Slot writes and actual immediate keypair releases preserve all hashed
owner relations throughout the evolving rotation states. -/
theorem rotationRun_owner_coherent {pid : PeerId} {d final : Device}
    {actions : List RotationAction} (steps : RotationRun pid d actions final)
    (coherent : HashedOwnersCoherent d) : HashedOwnersCoherent final := by
  induction steps with
  | nil => exact coherent
  | write d final change p rest resident tail ih =>
    apply ih
    apply peerWrite_owner_coherent d pid p (change.apply p) resident
    · cases change <;> rfl
    · cases change <;> rfl
    · exact coherent
  | put d middle final key rest release tail ih =>
    apply ih
    cases release with
    | null => exact coherent
    | present d id k resident live word =>
      exact releasedDevice_owner_coherent d id k true resident live coherent

end Leanux.Proofs.WG.Index
