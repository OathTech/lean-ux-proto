import Leanux.Proofs.WG.Index.ReleaseModel
import Leanux.Proofs.WG.Index.Allocation

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

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
