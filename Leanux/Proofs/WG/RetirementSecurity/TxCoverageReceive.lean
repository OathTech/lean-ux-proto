import Leanux.Proofs.WG.RetirementSecurity.TxCoverageRxCompletion

/-! Native receive admission does not alter allocated TX ownership. RX
allocation and index-owner bookkeeping retain the actual TX cell/queue projection. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCoverageReceive
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits ReceiveOccurrences
variable {locals : List TxLocalBatch}

theorem passive {action : WG.M α} (wire : SameView txCryptWire action)
    (queues : SameView handoffTxView action) : Preserves (TxCoverage locals) action := TxCoverageNative.wire queues wire


theorem index_lookup (kinds : List IndexKind) (index : Nat) :
    Preserves (TxCoverage locals) (indexLookup kinds index) := by
  apply (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.RxLookupHolders.«0».Leanux.Proofs.WG.RetirementSecurity.indexLookup_preserves)
  · apply hoare_liftIndex
    intro w d table before device
    apply TxCoverageNative.view_frame before
    dsimp only [TxCoverageNative.view]
    apply Prod.ext
    · funext pid; simp [handoffTxView,device]
    · funext id; simp [TxDisposition.txPackets,device]
  · intro owner
    exact passive (acquire_owner_wire owner) (acquire_owner_queues owner)

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves (TxCoverage locals) action :=
  passive (cryptWire_store same) (ownership_queues (ownershipPoints_kernel _ same))

theorem enqueue (id : SkbId) : Preserves (TxCoverage locals) (enqueuePerDeviceAndPeerRx id) :=
  passive (enqueue_wire id) (enqueue_queues id)

theorem peer_get (pid : PeerId) : Preserves (TxCoverage locals) (peerGet pid) := by
  apply passive
  · intro initial
    change Preserves (fun w => txCryptWire w = initial) _
    unfold peerGet refcountInc
    simp only [requireNotPending,branch,branchCmp,unsupported]
    repeat' crypt_wire_step initial
  · exact ownership_queues (peerGet_ownership pid)

theorem peer_put (pid : Option PeerId) : Preserves (TxCoverage locals) (peerPut pid) := TxCoverageNative.peer_put pid

theorem publication_middle (pid : PeerId) (id : SkbId) (state : PacketState) :
    Preserves (TxCoverage locals) (publicationMiddle pid id state) := by
  apply passive
  · intro initial
    change Preserves (fun w => txCryptWire w = initial) _
    unfold publicationMiddle
    simp only [invariant]
    repeat' first
      | (rx_retention_head setRxSkb; exact (set_rx_wire _ _).wp (· = initial))
      | crypt_wire_step initial
  · exact ownership_queues (rx_publication_middle_ownership pid id state)

theorem publish (id : SkbId) (state : PacketState) :
    Preserves (TxCoverage locals) (enqueuePerPeerRx (pure () : WG.M Unit) id state) := by
  rw [publication_factor]
  apply preserves_bind (get_rx id _)
  intro packet
  apply preserves_bind (indexOwner_peerDeref_preserves (.keypair packet.keypair) _)
  intro pid
  apply preserves_bind (peer_get pid)
  intro _
  apply preserves_bind (publication_middle pid id state)
  intro _
  exact peer_put (some pid)

theorem consume (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Preserves (TxCoverage locals) (consumeData msg src ds) := by
  have index := index_lookup (locals:=locals)
  have getKey (id : Option KeypairId) := passive (locals:=locals)
    (keyGet_cryptWire id) (keyGet_tx_queues id)
  have putKey (id : Option KeypairId) (now : Bool) := passive (locals:=locals)
    ((TxRing.keypairPut_frame id now).product (TxDisposition.keyPut_packets id now))
    ((keypairPut_protect id now).factor (fun s => s.2.2.1))
  have allocate (pkt : RxPacket) := passive (locals:=locals)
    (new_rx_wire pkt) (skb_queues _)
  have free (id : SkbId) := passive (locals:=locals)
    (free_rx_wire id) (skb_queues _)
  have enqueue := enqueue (locals:=locals)
  have publish := publish (locals:=locals)
  have pay := peer_put (locals:=locals)
  have peer (pid : PeerId) := getPeer_preserves pid (TxCoverage locals)
  have ambient {α : Type} (a : AmbientM α) : Preserves (TxCoverage locals) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [consumeData,WG.orM,keypairGetNull,branch,invariant]
    using [index,getKey,putKey,allocate,free,enqueue,publish,pay,peer,ambient]

theorem cpu_next : Preserves (TxCoverage locals) cpumaskNextOnline := by
  have device := store (locals:=locals)  getDev_sameWGStore
  have cpu (number : Int) : Preserves (TxCoverage locals)
      (modifyDev fun d => {d with handshakeLastCpu := number}) :=
    TxCoverageNative.modify_device _ (fun _ => rfl) (fun _ => rfl)
  have ambient {α : Type} (a : AmbientM α) : Preserves (TxCoverage locals) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [cpumaskNextOnline,branch] using [device,cpu,ambient]

theorem packet (msg : List UInt8) (src : SkbSource) :
    Preserves (TxCoverage locals) (packetReceive msg src) := by
  have header := store (locals:=locals)  ((prepareSkbHeader_sameWGWorld msg).factor wgStoreView)
  have ds (protocol : Nat) (bytes : List UInt8) :=
    store (locals:=locals) ((ipTunnelGetDsfield_sameWGWorld protocol bytes).factor wgStoreView)
  have device := store (locals:=locals)  getDev_sameWGStore
  have append : Preserves (TxCoverage locals)
      (modifyDev fun d => {d with handshakeQueue := d.handshakeQueue.produce (msg,src), handshakeQueueLen := d.handshakeQueueLen + 1}) :=
    TxCoverageNative.modify_device _ (fun _ => rfl) (fun _ => rfl)
  have data := consume (locals:=locals)  msg src
  have cpu := cpu_next (locals:=locals)
  have ambient {α : Type} (a : AmbientM α) : Preserves (TxCoverage locals) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [packetReceive,branch,invariant,unsupported,queueDeviceWork]
    using [header,ds,device,append,data,cpu,ambient]

theorem receive (msg : List UInt8) (src : SkbSource) :
    Preserves (TxCoverage locals) (wgReceive msg src) := by
  have packet := packet (locals:=locals)  msg src
  have ambient {α : Type} (a : AmbientM α) : Preserves (TxCoverage locals) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [wgReceive,branch,unsupported] using [packet,ambient]


end Leanux.Proofs.WG.RetirementSecurity.TxCoverageReceive
