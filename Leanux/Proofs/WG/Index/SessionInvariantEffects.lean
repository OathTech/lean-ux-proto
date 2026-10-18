import Leanux.Proofs.WG.Index.SessionInvariantModel
import Leanux.Proofs.WG.Index.SessionCoherenceModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Landed affiliation bounds every old slot below the allocation frontier;
no released old slot can name the new allocation, even with aliases. -/
theorem affiliation_session_fresh (d : Device) (pid : PeerId) (p : Peer)
    (hi : Affiliation.State.Inv (Affiliation.state d))
    (resident : d.peers[pid]? = some p) :
    SessionRotationFresh p d.nextKeypairId := by
  have below (kid : KeypairId)
      (selected : p.keypairCurrent = some kid ∨ p.keypairPrevious = some kid ∨
        p.keypairNext = some kid) : kid < d.nextKeypairId :=
    (hi.slots pid (Affiliation.peerCell p) kid
      (by simp [Affiliation.state, resident]) selected).1
  have current : some d.nextKeypairId ≠ p.keypairCurrent := by
    intro same
    exact Nat.lt_irrefl _ (below _ (Or.inl same.symm))
  have previous : some d.nextKeypairId ≠ p.keypairPrevious := by
    intro same
    exact Nat.lt_irrefl _ (below _ (Or.inr (Or.inl same.symm)))
  have next : some d.nextKeypairId ≠ p.keypairNext := by
    intro same
    exact Nat.lt_irrefl _ (below _ (Or.inr (Or.inr same.symm)))
  unfold SessionRotationFresh rotationPlan
  split
  · split <;> simp [rotateWithNext, rotateWithoutNext, rotationReleases,
      current, previous]
  · simp [rotateResponder, rotationReleases, next, previous]

/-- Hashed-owner residency turns the landed resident-key bound into the
allocation bound required by the index-table preservation contracts. -/
theorem affiliation_hashed_bound (d : Device)
    (hi : Affiliation.State.Inv (Affiliation.state d))
    (hc : HashedOwnersCoherent d) : KeypairOwnersBounded d := by
  intro entry member kid owner
  obtain ⟨pid, peer, word, resident, positive, key⟩ := hc entry member
  rw [owner] at key
  obtain ⟨keypair, stored, count⟩ := key
  exact hi.keyBound kid (Affiliation.keyCell keypair)
    (by simp [Affiliation.state, stored])

end Leanux.Proofs.WG.Index
