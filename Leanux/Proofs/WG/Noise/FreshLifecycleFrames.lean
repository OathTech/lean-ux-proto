import Leanux.Proofs.WG.Noise.FreshInstallFrames
import Leanux.Proofs.WG.Noise.ResponseTagFrames
import Leanux.Proofs.WG.Index.SessionAllocationFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

theorem freshInstallView_owner (tracked : PeerId) (d : Device) (owner : IndexOwner) (word : Option PeerId) :
    freshInstallView tracked (some (Index.writeOwnerWord d owner word)) = freshInstallView tracked (some d) := by
  cases owner with
  | keypair id => cases found : d.keypairs[id]? <;> simp only [Index.writeOwnerWord, found] <;> rfl
  | handshake pid =>
    cases found : d.peers[pid]? with
    | none => simp [Index.writeOwnerWord, found]
    | some p => simp only [Index.writeOwnerWord, found]; exact freshInstallView_write tracked pid d p _ found rfl

/-- Ordered slot clearing preserves the actual allocation cursor. Releases may
unhash or erase aliased keys, but do not allocate an identity. -/
theorem clearRun_allocation_cursor {pid : PeerId} {d final : Device}
    {slots : List ClearSlot} (run : ClearRun pid d slots final) :
    final.nextKeypairId = d.nextKeypairId := by
  induction run with
  | nil => rfl
  | cons d slot p middle final rest resident put tail ih =>
    have cursor := Index.clearPut_allocation_cursor put
    exact ih.trans (by simpa only [clearWrite] using cursor)

end Leanux.Proofs.WG.Noise
