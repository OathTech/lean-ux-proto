import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialBoundedFrames
import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierReceive

/-! Full native staging and receive-tail frames retain RX allocation
certificates. The key frontier follows the concrete C1 geometry projection. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AuthenticatedEffects Responder Origins.Retaining

theorem bounded_staging (pid : PeerId) : Preserves (Bounded h) (sendStagedPackets pid) :=
  bounded_frame
    (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.staged_geometry) pid).factor Prod.snd)
    (sendStagedPackets_core pid)
    (fun _ => ResidentMaterial.NativeFrames.lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.staged_geometry) pid))

theorem bounded_complete (pid : PeerId) (site : HiddenSite) :
    Preserves (Bounded h) (timersHandshakeComplete pid site) :=
  bounded_frame (TransportCarrier.handshakeComplete_rx pid site)
    (ResidentMaterial.core_of_same (pool_of_material (timersHandshakeComplete_material pid site)))
    (fun _ => ResidentMaterial.NativeFrames.lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.handshake_geometry) pid site))

theorem bounded_prepare_rest (pid : PeerId) (pkt : RxPacket) :
    Preserves (Bounded h) (RxCredits.prepareRest pid pkt) :=
  bounded_frame (TransportCarrier.prepareRest_rx pid pkt)
    (ResidentMaterial.core_of_same (prepareRest_core pid pkt))
    (fun _ => ResidentMaterial.NativeFrames.lower_prepare pid pkt)

theorem bounded_finish (pid : PeerId) (ready : Packets.RxReady) :
    Preserves (Bounded h) (Packets.rxFinish pid ready) :=
  bounded_frame (TransportCarrier.finish_rx pid ready)
    (ResidentMaterial.core_of_same (rxFinish_core pid ready))
    (fun _ => ResidentMaterial.NativeFrames.lower_finish pid ready)

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
