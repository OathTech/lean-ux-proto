import Leanux.Proofs.WG.Index.Allocation

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

def unhashKeypair (d : Device) (id : KeypairId) : Device :=
  { d with indexTable := removeOwner (.keypair id) d.indexTable }

/-- The actual ordered writes, including both unhashes on an immediate final put. -/
def releasedDevice (d : Device) (id : KeypairId) (k : Keypair) (now : Bool) : Device :=
  let unhashed := if now then unhashKeypair d id else d
  let decremented := { unhashed with keypairs := unhashed.keypairs.insert id { k with refcount := k.refcount - 1 } }
  if k.refcount = 1 then
    { unhashKeypair decremented id with keypairs := decremented.keypairs.erase id }
  else decremented

/-- A non-NULL peer word suffices for the mirror's device dereference here;
this does not assert residency of the peer it names or reachable ownership. -/
theorem keypairPut_exact (id : KeypairId) (now : Bool) (d : Device) (k : Keypair)
    (resident : d.keypairs[id]? = some k) (live : 0 < k.refcount)
    (word : k.peer ≠ none) :
    Returns (keypairPut (some id) now) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (releasedDevice d id k now)) := by
  rw [returns_iff]
  cases now <;> by_cases last : k.refcount = 1
  all_goals cases hp : k.peer <;> simp_all
  all_goals simp only [keypairPut]
  all_goals noise_vcgen [ IndexOwner.peerDeref, IndexOwner.peerWord,
    getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    refcountDecAndTest, branch, branchCmp, invariant, unsupported, indexRemove,
    _private.Leanux.WG.Peer.«0».Leanux.WG.unhashEntry]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [releasedDevice, unhashKeypair, removeOwner]
  all_goals subst_vars
  all_goals simp_all [releasedDevice, unhashKeypair, removeOwner, Std.TreeMap.getElem?_insert]
  all_goals grind only

end Leanux.Proofs.WG.Index
