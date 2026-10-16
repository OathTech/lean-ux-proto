import Leanux.Proofs.WG.Index.StoreFieldFrames
import Leanux.Proofs.WG.Index.ReleaseModel

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

theorem removeOwner_idem (owner : IndexOwner) (table : List IndexEntry) :
    removeOwner owner (removeOwner owner table) = removeOwner owner table := by
  simp [removeOwner, List.filter_filter]

theorem released_table (d : Device) (id : KeypairId) (k : Keypair) (now : Bool) :
    (releasedDevice d id k now).indexTable =
      if now || k.refcount == 1 then removeOwner (.keypair id) d.indexTable else d.indexTable := by
  cases now <;> by_cases last : k.refcount = 1 <;>
    simp [releasedDevice, unhashKeypair, last, removeOwner_idem]

theorem released_keypair (d : Device) (id : KeypairId) (k : Keypair) (now : Bool) :
    (releasedDevice d id k now).keypairs[id]? =
      if k.refcount = 1 then none else some { k with refcount := k.refcount - 1 } := by
  cases now <;> by_cases last : k.refcount = 1 <;>
    simp [releasedDevice, unhashKeypair, last]

theorem released_indices (d : Device) (id : KeypairId) (k : Keypair) (now : Bool)
    (unique : UniqueIndices d.indexTable) :
    UniqueIndices (releasedDevice d id k now).indexTable := by
  rw [released_table]
  split
  · exact remove_indices _ _ unique
  · exact unique

theorem released_owners (d : Device) (id : KeypairId) (k : Keypair) (now : Bool)
    (unique : UniqueOwners d.indexTable) :
    UniqueOwners (releasedDevice d id k now).indexTable := by
  rw [released_table]
  split
  · exact remove_owners _ _ unique
  · exact unique

theorem released_unhashed (d : Device) (id : KeypairId) (k : Keypair) (now : Bool)
    (removing : now = true ∨ k.refcount = 1) :
    ∀ e ∈ (releasedDevice d id k now).indexTable, e.owner ≠ .keypair id := by
  rw [released_table]
  have test : (now || k.refcount == 1) = true := by cases removing <;> simp_all
  rw [ite_eq_left test]
  exact remove_absent _ _

end Leanux.Proofs.WG.Index
