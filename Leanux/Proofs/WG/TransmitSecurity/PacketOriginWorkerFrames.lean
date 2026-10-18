import Leanux.Proofs.WG.TransmitSecurity.PacketOriginStagingFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDecryptFrames

/-! TX disposal retains origins of survivors. RX preparation and ring
selection preserve all stored TX material. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins.NativeFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity
set_option maxHeartbeats 600000

theorem transmit (pid : PeerId) : Preserves (Inv h) (txStep pid) := by
  unfold txStep WG.andM
  simp only [branch,invariant]
  repeat' first
    | (rx_retention_head PrevQueue.peek; exact store (prevQueuePeek_sameWGStore _))
    | (rx_retention_head createDataDone; exact frame (snapshot_wire (createDataDone_cryptWire _ _)))
    | origin_staging_frame

theorem poll : Preserves (Inv h) TxRing.pollSource := by
  unfold TxRing.pollSource
  repeat' origin_staging_frame

theorem prepare : Preserves (Inv h) RxWorkers.prepareSource := by
  have packet (pkt : RxPacket) : Preserves (Inv h) (decryptPacket pkt) :=
    frame (snapshot_wire (OccurrenceDecrypt.packet_wire pkt))
  have publish (id : SkbId) (state : PacketState) : Preserves (Inv h) (RxWorkers.publishSource id state) :=
    frame (snapshot_wire (OccurrenceDecrypt.publish_wire id state))
  have read (id : SkbId) : Preserves (Inv h) (getRxSkb id) :=
    frame (snapshot_wire (ReceiveOccurrences.get_rx_wire id))
  have write (id : SkbId) (f : RxPacket → RxPacket) : Preserves (Inv h) (setRxSkb id f) :=
    frame (snapshot_wire (ReceiveOccurrences.set_rx_wire id f))
  have device := store (h:=h) getDev_sameWGStore
  have ring (queue : PtrRing SkbId) : Preserves (Inv h)
      (modifyDev fun d => {d with decryptQueue := queue}) :=
    frame (PacketOrigins.modify _ (fun _ => rfl) (fun _ => rfl))
  have ambient {α : Type} (a : AmbientM α) : Preserves (Inv h) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [RxWorkers.prepareSource,branch,invariant] using [packet,publish,read,write,device,ring,ambient]

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins.NativeFrames
