import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceStagingFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationCountedCarrier

/-! Staged purge and overflow preserve the allocated packet store. These exact
native frames complement their staged queue partitions and drop-counter effects. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity.StagingOccurrences

theorem purge_packet_geometry (pid : PeerId) : SameView geometry (purgeStagedPackets pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold purgeStagedPackets
  repeat' staging_geometry_step initial

theorem trim_packet_geometry (pid : PeerId) : SameView geometry (xmitTrim pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold xmitTrim
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch]
  repeat' staging_geometry_step initial

theorem release_packet_geometry (peer : Option PeerId) :
    SameView geometry (HandshakeSecurity.StagedDisposal.releaseCut peer) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold HandshakeSecurity.StagedDisposal.releaseCut refcountDecAndTest
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,
    invariant,unsupported]
  repeat' staging_geometry_step initial

theorem purge_packet_material (pid : PeerId) : SameView PacketMaterial.view (purgeStagedPackets pid) :=
  PacketMaterial.of_packets ((purge_packet_geometry pid).factor Prod.snd)

theorem trim_packet_material (pid : PeerId) : SameView PacketMaterial.view (xmitTrim pid) :=
  PacketMaterial.of_packets ((trim_packet_geometry pid).factor Prod.snd)

theorem release_packet_material (peer : Option PeerId) :
    SameView PacketMaterial.view (HandshakeSecurity.StagedDisposal.releaseCut peer) :=
  PacketMaterial.of_packets ((release_packet_geometry peer).factor Prod.snd)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
