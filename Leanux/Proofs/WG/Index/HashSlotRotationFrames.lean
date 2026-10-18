import Leanux.Proofs.WG.Index.HashSlotModel
import Leanux.Proofs.WG.Index.OwnerCoherenceSlotRemovalFrames
import Leanux.Proofs.WG.Index.SessionCoherenceFrames
import Leanux.Proofs.WG.Noise.RotationClaims
import Leanux.Proofs.WG.Noise.SessionSource
import Leanux.Proofs.WG.Index.SessionInvariantEffects
import Leanux.Proofs.WG.Index.SessionSequenceSource


set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- A surviving hashed row was present initially, its key value is unchanged, and none of the rotation's immediate puts selected it. -/
theorem rotationRun_retained_key {pid : PeerId} {d final : Device}
    {actions : List RotationAction} (steps : RotationRun pid d actions final)
    (entry : IndexEntry) (kid : KeypairId)
    (member : entry ∈ final.indexTable) (owner : entry.owner = .keypair kid) :
    entry ∈ d.indexTable ∧ final.keypairs[kid]? = d.keypairs[kid]? ∧
      some kid ∉ rotationReleases actions := by
  induction steps with
  | nil => exact ⟨member,rfl,by simp [rotationReleases]⟩
  | write d final change p rest resident tail ih =>
    obtain ⟨old,key,excluded⟩ := ih member
    exact ⟨old,key,excluded⟩
  | put d middle final key rest release tail ih =>
    obtain ⟨middleMember,kept,excluded⟩ := ih member
    obtain ⟨old,_,unhashed⟩ := clearPut_retained_owner release entry middleMember
    have different : key ≠ some kid := fun same => unhashed kid same owner
    refine ⟨old,kept.trans (clearPut_other_key release kid different),?_⟩
    simp only [rotationReleases,List.mem_cons,not_or]
    exact ⟨Ne.symm different,excluded⟩

theorem rotationRun_other_peer {pid : PeerId} {d final : Device}
    {actions : List RotationAction} (steps : RotationRun pid d actions final)
    (target : PeerId) (different : pid ≠ target) :
    final.peers[target]? = d.peers[target]? := by
  induction steps with
  | nil => rfl
  | write d final change p rest resident tail ih =>
    simpa [rotationWriteDevice,Std.TreeMap.getElem?_insert,different] using ih
  | put d middle final key rest release tail ih =>
    rw [ih,clearPut_peers release]

end Leanux.Proofs.WG.Index
