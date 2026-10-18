import Leanux.Proofs.WG.Index.HashSlotModel
import Leanux.Proofs.WG.Index.OwnerCoherenceSlotRemovalFrames
import Leanux.Proofs.WG.Index.SessionCoherenceFrames
import Leanux.Proofs.WG.Noise.ClearSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

-- Frames
theorem clearPut_hashed_key {key : Option KeypairId} {d final : Device}
    (put : ClearPut key d final) (e : IndexEntry) (member : e ∈ final.indexTable)
    (kid : KeypairId) (owner : e.owner = .keypair kid) :
    final.keypairs[kid]? = d.keypairs[kid]? := by
  apply clearPut_other_key put kid
  intro selected
  exact (clearPut_retained_owner put e member).2.2 kid selected owner

theorem clearSlot_other_membership (slot : ClearSlot) (p : Peer) (kid : KeypairId)
    (member : some kid ∈ clearKeys p) (different : slot.read p ≠ some kid) :
    some kid ∈ clearKeys (slot.clear p) := by
  cases slot <;> simp_all [clearKeys, ClearSlot.read, ClearSlot.clear]
  all_goals rcases member with h | h | h <;> simp_all [eq_comm]


end Leanux.Proofs.WG.Index
