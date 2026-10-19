import Leanux.Proofs.WG.TransmitSecurity.StagedWorkerFrames
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginIngressFrames

/-! Native UDP admission retains staged origins through borrowed peer lookup,
RX queue admission and publication, with each saved peer write justified. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem enqueue_staged (id : SkbId) : SameView stagedAt (enqueuePerDeviceAndPeerRx id) := by
  intro initial
  unfold enqueuePerDeviceAndPeerRx
  apply preserves_bind ((Exact.skb _).wp (· = initial))
  intro _
  apply preserves_bind ((Exact.skb _).wp (· = initial))
  intro packet
  apply hoare_bind _ _ (Staged.read_saved (· = initial) packet.peer)
  intro peer
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .enqueuePeerQueueFull (peer.rxQueue.count ≥ MAX_QUEUED_PACKETS)) _)
  intro full
  split
  · exact hoare_consequence (hoare_pure _ _) (fun _ before => before.1) (fun _ _ before => before.2)
  · apply hoare_bind _ _ (Staged.write_saved (· = initial) packet.peer {peer with rxQueue := peer.rxQueue.enqueue id})
    intro _
    change Preserves (fun w => stagedAt w = initial) _
    simp only [branch,queueDeviceWork]
    repeat' first
      | (rx_retention_head cpumaskNextOnlineFrom; exact (Exact.store (cpumaskNextOnlineFrom_sameStore _)).wp (· = initial))
      | (rx_retention_head modifyDev; apply Exact.modify_preserves; intro d; rfl)
      | staged_exact_step initial

theorem receive_publish (id : SkbId) (state : PacketState) :
    Preserves (Inv h) (enqueuePerPeerRx (pure () : WG.M Unit) id state) := by
  rw [PublicationFrontier.enqueuePerPeerRx_factor]
  exact preserves_bind (publish_rx id state)
    (fun pid => preserves_bind (preserves_pure ()) (fun _ => peer_put (some pid)))

theorem receive_admit (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves (Inv h) (consumeData msg src ds) := by
  have index (kinds : List IndexKind) (number : Nat) : Preserves (Inv h) (indexLookup kinds number) :=
    frame (PacketOrigins.epoch_ring ((OccurrenceHandshake.index_lookup_wire kinds number).factor Prod.fst)) (Staged.lookup kinds number)
  have getKey := key_get (h:=h)
  have putKey := key_put (h:=h)
  have allocate (pkt : RxPacket) : Preserves (Inv h) (newRxSkb pkt) := skb _
  have free (id : SkbId) : Preserves (Inv h) (freeRxSkb id) := skb _
  have enqueue (id : SkbId) : Preserves (Inv h) (enqueuePerDeviceAndPeerRx id) :=
    frame (PacketOrigins.epoch_ring ((ReceiveOccurrences.enqueue_wire id).factor Prod.fst)) (Staged.of_view _ (enqueue_staged id))
  have publish := receive_publish (h:=h)
  have pay := peer_put (h:=h)
  have peer := read_peer (h:=h)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Inv h) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [consumeData,WG.orM,keypairGetNull,branch,invariant]
    using [index,getKey,putKey,allocate,free,enqueue,publish,pay,peer,ambient]

theorem cpu_next : Preserves (Inv h) cpumaskNextOnline := by
  unfold cpumaskNextOnline
  repeat' staged_origin_native

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
    modify_device _ (fun _ => rfl) (fun _ => rfl)
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

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
