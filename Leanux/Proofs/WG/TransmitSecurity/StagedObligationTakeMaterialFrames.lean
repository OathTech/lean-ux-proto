import Leanux.Proofs.WG.TransmitSecurity.StagedObligationTakeFrames
import Leanux.Proofs.WG.TransmitSecurity.PacketOrigins

/-! The staging take changes a peer queue, preserving every allocated packet's
immutable material and the device epoch. No whole-world equality is assumed. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins Queues
open HandshakeSecurity.StagedConservation

theorem take_material_views (r : Take.Receipt) (native : r.Valid) :
    Packets.epoch r.run.after = Packets.epoch r.run.before ∧
      PacketMaterial.view r.run.after = PacketMaterial.view r.run.before := by
  cases result : r.run.value with
  | none =>
    have run : ((Take.takePrefix r.pid).run r.run.before).run r.run.ambientBefore =
        .ok ((none,r.run.after),r.run.ambientAfter) := by
      rw [←result]
      exact native
    obtain ⟨_,_,_,_,_,same,_⟩ := Take.take_none _ _ _ _ _ run
    rw [same]
    exact ⟨rfl,rfl⟩
  | some peer =>
    have run : ((Take.takePrefix r.pid).run r.run.before).run r.run.ambientBefore =
        .ok ((some peer,r.run.after),r.run.ambientAfter) := by
      rw [←result]
      exact native
    obtain ⟨d,device,_,_,after,_⟩ := Take.take_some _ _ _ _ _ peer run
    refine ⟨?_,?_⟩
    · simp [Packets.epoch,device,after]
    · funext id
      simp [PacketMaterial.view,TxDisposition.txPackets,device,after]

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
