import Leanux.Proofs.WG.RetirementSecurity.TxWorkNetworkSyscall
import Leanux.Proofs.WG.RetirementSecurity.TxCoverageBoundaryTraffic

/-! Native UDP admission preserves TX service, including RX queue refusal,
dead publication and final peer release. No receive success is assumed. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open ReceiveOccurrences

theorem rx_admission_work (id : SkbId) : SameView queued (enqueuePerDeviceAndPeerRx id) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold enqueuePerDeviceAndPeerRx
  simp (config:={zeta:=false}) only [branch,queueDeviceWork]
  repeat' first
    | (rx_retention_head setRxSkb; exact (skb_work _).wp (·=initial))
    | (rx_retention_head getRxSkb; exact get_rx _ _)
    | (rx_retention_head cpumaskNextOnlineFrom; exact (store (cpumaskNextOnlineFrom_sameStore _)).wp (·=initial))
    | tx_work_step initial

theorem rx_middle_work (pid : PeerId) (id : SkbId) (state : PacketState) :
    SameView queued (publicationMiddle pid id state) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold publicationMiddle
  simp only [invariant]
  repeat' first
    | (rx_retention_head setRxSkb; exact (skb_work _).wp (·=initial))
    | tx_work_step initial

theorem rx_middle_service (pid : PeerId) (id : SkbId) (state : PacketState) :
    Preserves (Obligations crypt tx) (publicationMiddle pid id state) := by
  apply passive ?_ (ownership_queues (rx_publication_middle_ownership pid id state)) (rx_middle_work pid id state)
  intro initial
  change Preserves (fun w=>txCryptWire w=initial) _
  unfold publicationMiddle
  simp only [invariant]
  repeat' first
    | (rx_retention_head setRxSkb; exact (set_rx_wire _ _).wp (·=initial))
    | crypt_wire_step initial

theorem rx_publish_service (id : SkbId) (state : PacketState) :
    Preserves (Obligations crypt tx) (enqueuePerPeerRx (pure () : WG.M Unit) id state) := by
  rw [publication_factor]
  apply preserves_bind (get_rx id _)
  intro packet
  apply preserves_bind (indexOwner_peerDeref_preserves (.keypair packet.keypair) _)
  intro pid
  have wire : SameView txCryptWire (peerGet pid) := by
    intro initial
    change Preserves (fun w=>txCryptWire w=initial) _
    unfold peerGet refcountInc
    simp only [requireNotPending,branch,branchCmp,unsupported]
    repeat' crypt_wire_step initial
  apply preserves_bind (passive wire (ownership_queues (peerGet_ownership pid)) (TxWork.peer_get pid))
  intro _
  apply preserves_bind (rx_middle_service pid id state)
  intro _
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases result
  exact before.peer_put (some pid) a b run

theorem consume_service (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves (Obligations crypt tx) (consumeData msg src ds) := by
  have index (kinds : List IndexKind) (id : Nat) : Preserves (Obligations crypt tx) (indexLookup kinds id) :=
    passive_contents (OccurrenceHandshake.index_lookup_wire kinds id)
      (OccurrenceHandshake.index_lookup_contents kinds id) (index_lookup_work kinds id)
  have getKey := key_get_service (crypt:=crypt) (tx:=tx)
  have putKey (id : Option KeypairId) (now : Bool) := passive (crypt:=crypt) (tx:=tx)
    ((TxRing.keypairPut_frame id now).product (TxDisposition.keyPut_packets id now))
    ((keypairPut_protect id now).factor (fun s=>s.2.2.1)) (key_put id now)
  have allocate (pkt : RxPacket) := passive (crypt:=crypt) (tx:=tx)
    (new_rx_wire pkt) (skb_queues _) (skb_work _)
  have free (id : SkbId) := passive (crypt:=crypt) (tx:=tx)
    (free_rx_wire id) (skb_queues _) (skb_work _)
  have enqueue (id : SkbId) := passive (crypt:=crypt) (tx:=tx)
    (enqueue_wire id) (enqueue_queues id) (rx_admission_work id)
  have publish := rx_publish_service (crypt:=crypt) (tx:=tx)
  have pay (pid : Option PeerId) : Preserves (Obligations crypt tx) (peerPut pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    cases result
    exact before.peer_put pid a b run
  have peer (pid : PeerId) := getPeer_preserves pid (Obligations crypt tx)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Obligations crypt tx) (monadLift a : WG.M α) := hoare_liftAmbient a _
  rxstack_preserves_source [consumeData,WG.orM,keypairGetNull,branch,invariant]
    using [index,getKey,putKey,allocate,free,enqueue,publish,pay,peer,ambient]

theorem receive_cpu_service : Preserves (Obligations crypt tx) cpumaskNextOnline := by
  have device := service_store (crypt:=crypt) (tx:=tx) getDev_sameWGStore
  have cpu (number : Int) : Preserves (Obligations crypt tx)
      (modifyDev fun d=>{d with handshakeLastCpu:=number}) :=
    service_device _ (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Obligations crypt tx) (monadLift a : WG.M α) := hoare_liftAmbient a _
  rxstack_preserves_source [cpumaskNextOnline,branch] using [device,cpu,ambient]

theorem packet_receive_service (msg : List UInt8) (src : SkbSource) :
    Preserves (Obligations crypt tx) (packetReceive msg src) := by
  have header := service_store (crypt:=crypt) (tx:=tx) ((prepareSkbHeader_sameWGWorld msg).factor wgStoreView)
  have ds (protocol : Nat) (bytes : List UInt8) := service_store (crypt:=crypt) (tx:=tx)
    ((ipTunnelGetDsfield_sameWGWorld protocol bytes).factor wgStoreView)
  have device := service_store (crypt:=crypt) (tx:=tx) getDev_sameWGStore
  have append : Preserves (Obligations crypt tx)
      (modifyDev fun d=>{d with handshakeQueue:=d.handshakeQueue.produce (msg,src),handshakeQueueLen:=d.handshakeQueueLen+1}) :=
    service_device _ (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
  have data := consume_service (crypt:=crypt) (tx:=tx) msg src
  have cpu := receive_cpu_service (crypt:=crypt) (tx:=tx)
  have ambient {α : Type} (a : AmbientM α) : Preserves (Obligations crypt tx) (monadLift a : WG.M α) := hoare_liftAmbient a _
  rxstack_preserves_source [packetReceive,branch,invariant,unsupported,queueDeviceWork]
    using [header,ds,device,append,data,cpu,ambient]

theorem ingress_service (msg : List UInt8) (src : SkbSource) :
    Preserves (Obligations crypt tx) (wgReceive msg src) := by
  have packet := packet_receive_service (crypt:=crypt) (tx:=tx) msg src
  have ambient {α : Type} (a : AmbientM α) : Preserves (Obligations crypt tx) (monadLift a : WG.M α) := hoare_liftAmbient a _
  rxstack_preserves_source [wgReceive,branch,unsupported] using [packet,ambient]

theorem serving_ingress (msg : List UInt8) (src : SkbSource) :
    Preserves (Serving locals crypt tx) (wgReceive msg src) :=
  serving_join (ingress_service msg src)
    (TxCovered.join (RxPollOccurrences.join (ReceiveIngressCall.erases (.udp msg src))
      (ReceiveIngressCall.allocation (.udp msg src)) (ReceiveOccurrences.receive msg src))
      (TxCoverageReceive.receive msg src))

end Leanux.Proofs.WG.RetirementSecurity.TxWork
