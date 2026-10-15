import Leanux.Proofs.WG.Config.RemoveFlagModel
import Leanux.Proofs.WG.Config.QuietFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

theorem collisionRemoval_retained {pid : PeerId} {d final : Device} {p : Peer}
    (effect : CollisionRemovalEffect pid d p final) (retained : 1 < p.refcount) :
    ∃ q, final.peers[pid]? = some q ∧ q.refcount = p.refcount - 1 := by
  obtain ⟨removed, removal, cleared, steps, rfl⟩ := effect
  let cleaned := quietCleanupPeer { erasePeerList p.allowedipsList p with isDead := true }
  have count : cleaned.refcount = p.refcount := by
    simp only [cleaned, quietCleanup_refcount, erasePeerList_refcount]
  have last : cleaned.refcount ≠ 1 := by omega
  refine ⟨{ cleaned with refcount := cleaned.refcount - 1 }, ?_, ?_⟩
  · change (Index.releasedPeerDevice _ pid cleaned).peers[pid]? = _
    simp [Index.releasedPeerDevice, last]
  · simp only [count]

theorem removeFlag_residency {pid : PeerId} {d final : Device} {p : Peer}
    (effect : RemoveFlagEffect pid d p final) :
    (final.peers[pid]? = none ↔ p.refcount = 1) ∧
    (p.refcount ≠ 1 → ∃ q, final.peers[pid]? = some q ∧ q.refcount = p.refcount - 1) := by
  obtain ⟨removed, q, removal, resident, count, rfl⟩ := effect
  constructor
  · by_cases last : p.refcount = 1
    · simp [Index.releasedPeerDevice, count, last]
    · simp [Index.releasedPeerDevice, count, last]
  · intro retained
    refine ⟨{ q with refcount := q.refcount - 1 }, ?_, ?_⟩
    · simp [Index.releasedPeerDevice, count, retained]
    · simp only [count]

end Leanux.Proofs.WG.Config
