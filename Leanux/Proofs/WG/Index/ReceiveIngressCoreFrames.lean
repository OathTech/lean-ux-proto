import Leanux.Proofs.WG.Index.ReceiveCoreFrames
import Leanux.Proofs.WG.Queues.AdmissionReceive

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReceiveIngressCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem append_fields (msg : List UInt8) (src : SkbSource) :
    SameView ConfigurationIndex.fields (modifyDev (appendHandshakeQueue msg src)) :=
  ConfigurationIndex.modifyDev_fields (appendHandshakeQueue msg src) (fun _ => rfl)

theorem cpu_fields (cpu : Int) :
    SameView ConfigurationIndex.fields (modifyDev (setHandshakeCpu cpu)) :=
  ConfigurationIndex.modifyDev_fields (setHandshakeCpu cpu) (fun _ => rfl)

/-- Local variant of the admission front's CPU frame, retaining the index fields. -/
theorem cpumask_view_index_variant : SameView ConfigurationIndex.fields cpumaskNextOnline := by
  apply SameView.of_wp
  intro initial
  change Preserves (fun w => ConfigurationIndex.fields w = initial) cpumaskNextOnline
  unfold cpumaskNextOnline
  simp only [branch]
  repeat' first
    | (rx_retention_head getDev; exact (ReceiveCompletion.store_fields getDev_sameWGStore).wp (· = initial))
    | (rx_retention_head modifyDev
       exact (cpu_fields _).wp (· = initial))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

/-- Local variant of AdmissionReceive.packet_view for the actual pre-admission fields. -/
theorem packet_view_index_variant (msg : List UInt8) (src : SkbSource) :
    SameView ConfigurationIndex.fields (AdmissionReceive.packetFront msg src) := by
  apply SameView.of_wp
  intro initial
  change Preserves (fun w => ConfigurationIndex.fields w = initial)
    (AdmissionReceive.packetFront msg src)
  unfold AdmissionReceive.packetFront
  simp only [branch,queueDeviceWork,invariant,unsupported]
  repeat' first
    | (rx_retention_head prepareSkbHeader
       exact ((prepareSkbHeader_sameWGWorld _).factor ConfigurationIndex.fields).wp (· = initial))
    | (rx_retention_head ipTunnelGetDsfield
       exact ((ipTunnelGetDsfield_sameWGWorld _ _).factor ConfigurationIndex.fields).wp (· = initial))
    | (rx_retention_head modifyDev
       exact (append_fields msg src).wp (· = initial))
    | (rx_retention_head cpumaskNextOnline; exact cpumask_view_index_variant.wp (· = initial))
    | (rx_retention_head getDev; exact (ReceiveCompletion.store_fields getDev_sameWGStore).wp (· = initial))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

/-- Local variant of AdmissionReceive.front_view; original socket/header errors remain. -/
theorem front_view_index_variant (msg : List UInt8) (src : SkbSource) :
    SameView ConfigurationIndex.fields (AdmissionReceive.front msg src) := by
  apply SameView.of_wp
  intro initial
  change Preserves (fun w => ConfigurationIndex.fields w = initial) (AdmissionReceive.front msg src)
  unfold AdmissionReceive.front
  simp only [branch,unsupported]
  repeat' first
    | (rx_retention_head AdmissionReceive.packetFront
       exact (packet_view_index_variant _ _).wp (· = initial))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.Index.ReceiveIngressCore
