import Leanux.Proofs.WG.Index.ReleaseEffects

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

theorem released_owners_bounded (d : Device) (id : KeypairId) (k : Keypair) (now : Bool)
    (bounded : KeypairOwnersBounded d) :
    KeypairOwnersBounded (releasedDevice d id k now) := by
  intro e member other owner
  rw [released_next]
  apply bounded e _ other owner
  rw [released_table] at member
  split at member
  · exact (List.mem_filter.mp member).1
  · exact member

theorem released_store_bounded (d : Device) (id : KeypairId) (k : Keypair) (now : Bool)
    (resident : d.keypairs[id]? = some k) (bounded : KeypairStoreBounded d) :
    KeypairStoreBounded (releasedDevice d id k now) := by
  intro other keypair found
  rw [released_next]
  by_cases same : id = other
  · subst other
    exact bounded id k resident
  · rw [released_other_keypair d id other k now same] at found
    exact bounded other keypair found

end Leanux.Proofs.WG.Index
