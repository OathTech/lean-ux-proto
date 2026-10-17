import Leanux.Proofs.WG.Index.StoreFieldFrames
import Leanux.Proofs.WG.Index.PeerWordSource
import Leanux.Proofs.WG.Index.Lookup

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem lookupFinish_live (index : Nat) (owner : IndexOwner) (d : Device)
    (pid : PeerId) (p : Peer) (word : ownerWord d owner = some (some pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) :
    Returns (lookupFinish (some { index, owner }, true)) (fun w => w.k.wg = some d)
      (fun result w => result = some (owner, pid) ∧
        w.k.wg = some (writeOwnerWord (acquirePeer d pid p) owner (some pid))) := by
  have hr := (returns_iff _ _ _).mp (peerWord_returns owner d (some pid) word)
  have hg := (returns_iff _ _ _).mp (peerGet_live_returns d pid p resident live bounded)
  have hs := fun value => (returns_iff _ _ _).mp
    (setPeerWord_returns owner (acquirePeer d pid p) (some pid) value
      (acquirePeer_word d pid p owner (some pid) resident word))
  rw [returns_iff]
  simp [lookupFinish, branch, bind_assoc]
  mvcgen [invariant, hr, hg, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals subst_vars
  all_goals mvcgen [invariant, hg, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals grind only

theorem lookupPrefix_matching (kinds : List IndexKind) (index : Nat) (owner : IndexOwner)
    (d : Device) (table : d.indexTable.find? (·.index == index) = some { index, owner })
    (permitted : kinds.contains (IndexEntry.kind { index, owner }) = true) :
    Returns (lookupPrefix kinds index) (fun w => w.k.wg = some d)
      (fun result w => result = (some { index, owner }, true) ∧ w.k.wg = some d) := by
  simpa [selectedState, bucket_find, table, permitted] using lookupPrefix_returns kinds index d

theorem indexLookup_null (kinds : List IndexKind) (index : Nat) (owner : IndexOwner)
    (d : Device) (table : d.indexTable.find? (·.index == index) = some { index, owner })
    (permitted : kinds.contains (IndexEntry.kind { index, owner }) = true)
    (word : ownerWord d owner = some none) :
    Returns (indexLookup kinds index) (fun w => w.k.wg = some d)
      (fun result w => result = none ∧ w.k.wg = some (writeOwnerWord d owner none)) := by
  rw [indexLookup_factor]
  apply returns_bind _ _ (lookupPrefix_matching kinds index owner d table permitted)
  intro state w pre
  obtain ⟨heq, hd⟩ := pre
  subst state
  exact lookupFinish_null index owner d word w hd

theorem indexLookup_dead (kinds : List IndexKind) (index : Nat) (owner : IndexOwner)
    (d : Device) (table : d.indexTable.find? (·.index == index) = some { index, owner })
    (permitted : kinds.contains (IndexEntry.kind { index, owner }) = true)
    (pid : PeerId) (p : Peer) (word : ownerWord d owner = some (some pid))
    (resident : d.peers[pid]? = some p) (dead : p.refcount = 0) :
    Returns (indexLookup kinds index) (fun w => w.k.wg = some d)
      (fun result w => result = none ∧ w.k.wg = some (writeOwnerWord d owner none)) := by
  rw [indexLookup_factor]
  apply returns_bind _ _ (lookupPrefix_matching kinds index owner d table permitted)
  intro state w pre
  obtain ⟨heq, hd⟩ := pre
  subst state
  exact lookupFinish_dead index owner d pid p word resident dead w hd

theorem indexLookup_live (kinds : List IndexKind) (index : Nat) (owner : IndexOwner)
    (d : Device) (table : d.indexTable.find? (·.index == index) = some { index, owner })
    (permitted : kinds.contains (IndexEntry.kind { index, owner }) = true)
    (pid : PeerId) (p : Peer) (word : ownerWord d owner = some (some pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) :
    Returns (indexLookup kinds index) (fun w => w.k.wg = some d)
      (fun result w => result = some (owner, pid) ∧
        w.k.wg = some (writeOwnerWord (acquirePeer d pid p) owner (some pid))) := by
  rw [indexLookup_factor]
  apply returns_bind _ _ (lookupPrefix_matching kinds index owner d table permitted)
  intro state w pre
  obtain ⟨heq, hd⟩ := pre
  subst state
  exact lookupFinish_live index owner d pid p word resident live bounded w hd

end Leanux.Proofs.WG.Index
