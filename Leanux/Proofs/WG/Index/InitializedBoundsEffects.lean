import Leanux.Proofs.WG.Index.InitializedBoundsModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.InitializedBounds
open Lean Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

/-! Pure effects: precisely the smaller inputs used by session freshness and
hashed allocation bounds. Existing stronger affiliation lemmas stay unchanged. -/
theorem slots_session_fresh (d : Device) (pid : PeerId) (p : Peer)
    (slots : CurrentSlots.SlotInv (Affiliation.state d))
    (resident : d.peers[pid]? = some p) :
    SessionRotationFresh p d.nextKeypairId := by
  intro member
  have positive := List.count_pos_iff.mpr member
  have bounded := Noise.rotationReleases_slot_count p
    (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) d.nextKeypairId d.nextKeypairId
  have old : some d.nextKeypairId ∈ Noise.clearKeys p :=
    List.count_pos_iff.mp (Nat.lt_of_lt_of_le positive bounded)
  exact Nat.lt_irrefl _ (Noise.initial_slot_before_cursor pid d p resident slots _ old)

theorem store_hashed_bound (d : Device) (bounded : KeypairStoreBounded d)
    (coherent : HashedOwnersCoherent d) : KeypairOwnersBounded d := by
  intro entry member kid owner
  obtain ⟨pid,peer,word,resident,positive,key⟩ := coherent entry member
  rw [owner] at key
  obtain ⟨keypair,stored,count⟩ := key
  exact bounded kid keypair stored


end Leanux.Proofs.WG.Index.InitializedBounds
