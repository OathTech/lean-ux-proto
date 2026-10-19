import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestoreFrames
import Leanux.Proofs.WG.TransmitSecurity.PacketOrigins

/-! Whole-batch restoration changes only the staged peer queue among the
obligation projections; allocated packet material and epoch remain exact. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Queues

theorem restore_material_views (r : HandshakeSecurity.StagedConservation.Restore.Receipt)
    (native : r.Valid) :
    Packets.epoch r.run.after = Packets.epoch r.run.before ∧
      PacketMaterial.view r.run.after = PacketMaterial.view r.run.before := by
  obtain ⟨d,p,device,_,after,_⟩ :=
    HandshakeSecurity.NonceRejection.restoration r.pid r.packets r.run native
  refine ⟨?_,?_⟩
  · simp [Packets.epoch,device,after]
  · funext id
    simp [PacketMaterial.view,TxDisposition.txPackets,device,after]

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
