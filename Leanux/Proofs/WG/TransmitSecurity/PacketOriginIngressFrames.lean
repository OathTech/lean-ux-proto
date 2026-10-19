import Leanux.Proofs.WG.TransmitSecurity.PacketOriginHandshakeFrames

/-! UDP ingress allocates RX packets and changes RX publication state while
retaining the material and allocation origins of every resident TX packet. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins.NativeFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity
set_option maxHeartbeats 600000

theorem receive_publish (id : SkbId) (state : PacketState) :
    Preserves (Inv h) (enqueuePerPeerRx (pure () : WG.M Unit) id state) := by
  rw [PublicationFrontier.enqueuePerPeerRx_factor]
  exact preserves_bind (frame (snapshot_wire (OccurrenceDecrypt.publish_wire id state)))
    (fun pid => preserves_bind (preserves_pure ()) (fun _ => peer_put (some pid)))

theorem receive_admit (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves (Inv h) (consumeData msg src ds) := by
  have index (kinds : List IndexKind) (number : Nat) : Preserves (Inv h) (indexLookup kinds number) :=
    frame (snapshot_wire (OccurrenceHandshake.index_lookup_wire kinds number))
  have getKey := key_get (h:=h)
  have putKey := key_put (h:=h)
  have allocate (pkt : RxPacket) : Preserves (Inv h) (newRxSkb pkt) :=
    frame (snapshot_wire (ReceiveOccurrences.new_rx_wire pkt))
  have free (id : SkbId) : Preserves (Inv h) (freeRxSkb id) :=
    frame (snapshot_wire (ReceiveOccurrences.free_rx_wire id))
  have enqueue (id : SkbId) : Preserves (Inv h) (enqueuePerDeviceAndPeerRx id) :=
    frame (snapshot_wire (ReceiveOccurrences.enqueue_wire id))
  have publish := receive_publish (h:=h)
  have pay := peer_put (h:=h)
  have peer := read_peer (h:=h)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Inv h) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [consumeData,WG.orM,keypairGetNull,branch,invariant]
    using [index,getKey,putKey,allocate,free,enqueue,publish,pay,peer,ambient]

theorem cpu_next : Preserves (Inv h) cpumaskNextOnline := by
  have device := store (h:=h) getDev_sameWGStore
  have cpu (number : Int) : Preserves (Inv h)
      (modifyDev fun d => {d with handshakeLastCpu := number}) :=
    frame (PacketOrigins.modify _ (fun _ => rfl) (fun _ => rfl))
  have ambient {α : Type} (a : AmbientM α) : Preserves (Inv h) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [cpumaskNextOnline,branch] using [device,cpu,ambient]

theorem packet_receive (msg : List UInt8) (src : SkbSource) :
    Preserves (Inv h) (packetReceive msg src) := by
  have header := store (h:=h) ((prepareSkbHeader_sameWGWorld msg).factor wgStoreView)
  have ds (protocol : Nat) (bytes : List UInt8) :=
    store (h:=h) ((ipTunnelGetDsfield_sameWGWorld protocol bytes).factor wgStoreView)
  have device := store (h:=h) getDev_sameWGStore
  have append : Preserves (Inv h)
      (modifyDev fun d => {d with
        handshakeQueue := d.handshakeQueue.produce (msg,src)
        handshakeQueueLen := d.handshakeQueueLen + 1}) :=
    frame (PacketOrigins.modify _ (fun _ => rfl) (fun _ => rfl))
  have data := receive_admit (h:=h) msg src
  have cpu := cpu_next (h:=h)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Inv h) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [packetReceive,branch,invariant,unsupported,queueDeviceWork]
    using [header,ds,device,append,data,cpu,ambient]

theorem receive (msg : List UInt8) (src : SkbSource) : Preserves (Inv h) (wgReceive msg src) := by
  have packet := packet_receive (h:=h) msg src
  have ambient {α : Type} (a : AmbientM α) : Preserves (Inv h) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [wgReceive,branch,unsupported] using [packet,ambient]

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins.NativeFrames
