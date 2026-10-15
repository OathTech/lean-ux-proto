import Leanux.Proofs.WG.Index.OwnerWordModel

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Every hashed keypair owner precedes the next allocation identity. -/
def KeypairOwnersBounded (d : Device) : Prop :=
  ∀ e ∈ d.indexTable, ∀ id, e.owner = .keypair id → id < d.nextKeypairId

def createdDevice (d : Device) (counter : Nat) (peer : Option PeerId) : Device :=
  { d with
    nextKeypairId := d.nextKeypairId + 1
    keypairs := d.keypairs.insert d.nextKeypairId { internalId := counter + 1, peer } }

theorem bounded_fresh (d : Device) (bounded : KeypairOwnersBounded d) :
    ∀ e ∈ d.indexTable, e.owner ≠ .keypair d.nextKeypairId := by
  intro e member same
  have impossible := bounded e member d.nextKeypairId same
  exact Nat.lt_irrefl _ impossible

theorem created_bounded (d : Device) (counter : Nat) (peer : Option PeerId)
    (bounded : KeypairOwnersBounded d) :
    KeypairOwnersBounded (createdDevice d counter peer) := by
  intro e member id owner
  have old := bounded e member id owner
  exact Nat.lt_succ_of_lt old

/-- Every resident keypair is below the next allocation identity. -/
def KeypairStoreBounded (d : Device) : Prop :=
  ∀ id keypair, d.keypairs[id]? = some keypair → id < d.nextKeypairId

theorem store_bound_absent (d : Device) (bounded : KeypairStoreBounded d) :
    d.keypairs[d.nextKeypairId]? = none := by
  cases h : d.keypairs[d.nextKeypairId]? with
  | none => rfl
  | some keypair => exact False.elim (Nat.lt_irrefl _ (bounded _ _ h))

theorem created_store_bounded (d : Device) (counter : Nat) (peer : Option PeerId)
    (bounded : KeypairStoreBounded d) :
    KeypairStoreBounded (createdDevice d counter peer) := by
  intro id keypair resident
  by_cases same : d.nextKeypairId = id
  · subst id
    exact Nat.lt_succ_self _
  · have old : d.keypairs[id]? = some keypair := by
      simpa [createdDevice, Std.TreeMap.getElem?_insert, same] using resident
    exact Nat.lt_succ_of_lt (bounded _ _ old)

theorem created_peer_word (d : Device) (counter : Nat) (peer : Option PeerId) :
    ownerWord (createdDevice d counter peer) (.keypair d.nextKeypairId) = some peer := by
  simp [ownerWord, createdDevice]

end Leanux.Proofs.WG.Index
