import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextNativeRxCompletion

/-! Receive allocation and queue publication preserve queued TX batch
readiness. Empty-peer cleanup is covered by the native payment frame. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Receive
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits ReceiveOccurrences

theorem passive {action : WG.M α} (wire : SameView txCryptWire action)
    (queues : SameView handoffTxView action) : Preserves Inv action := Native.wire queues wire

local notation "occurrence_passive" => passive

theorem index_lookup (kinds : List IndexKind) (index : Nat) :
    Preserves Inv (indexLookup kinds index) := by
  apply (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.RxLookupHolders.«0».Leanux.Proofs.WG.RetirementSecurity.indexLookup_preserves)
  · apply hoare_liftIndex
    intro w d table before device
    apply before.frame
    dsimp only [view]
    apply Prod.ext
    · funext pid; simp [handoffTxView,device]
    · funext id; simp [TxDisposition.txPackets,device]
  · intro owner
    exact passive (acquire_owner_wire owner) (acquire_owner_queues owner)

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves Inv action :=
  occurrence_passive (cryptWire_store same) (ownership_queues (ownershipPoints_kernel _ same))

theorem get_rx (id : SkbId) (P : WGWorld → Prop) : Preserves P (getRxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact (Packets.getRxSkb_current id w v result a b run).1 ▸ before

theorem enqueue_wire (id : SkbId) : SameView txCryptWire (enqueuePerDeviceAndPeerRx id) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold enqueuePerDeviceAndPeerRx
  simp (config := {zeta := false}) only [branch,queueDeviceWork]
  repeat' first
    | (rx_retention_head setRxSkb; exact (set_rx_wire _ _).wp (· = initial))
    | (rx_retention_head getRxSkb; exact get_rx _ _)
    | (rx_retention_head cpumaskNextOnlineFrom; exact (cryptWire_store (cpumaskNextOnlineFrom_sameStore _)).wp (· = initial))
    | crypt_wire_step initial

theorem enqueue_queues (id : SkbId) : SameView handoffTxView (enqueuePerDeviceAndPeerRx id) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold enqueuePerDeviceAndPeerRx
  simp (config := {zeta := false}) only [branch,queueDeviceWork]
  repeat' first
    | (rx_retention_head setRxSkb; exact (skb_queues _).wp (· = initial))
    | (rx_retention_head getRxSkb; exact get_rx _ _)
    | (rx_retention_head getDev; exact (getDev_sameWGStore.of_factor
        (fun s => handoffTxView {dev := s.dev}) handoffTxView (fun _ => rfl)).wp (· = initial))
    | (rx_retention_head cpumaskNextOnlineFrom; exact ((cpumaskNextOnlineFrom_sameStore _).of_factor
        (fun s => handoffTxView {dev := s.dev}) handoffTxView (fun _ => rfl)).wp (· = initial))
    | crypt_queue_step initial

theorem enqueue (id : SkbId) : Preserves Inv (enqueuePerDeviceAndPeerRx id) :=
  occurrence_passive (enqueue_wire id) (enqueue_queues id)

theorem peer_get (pid : PeerId) : Preserves Inv (peerGet pid) := by
  apply occurrence_passive
  · intro initial
    change Preserves (fun w => txCryptWire w = initial) _
    unfold peerGet refcountInc
    simp only [requireNotPending,branch,branchCmp,unsupported]
    repeat' crypt_wire_step initial
  · exact ownership_queues (peerGet_ownership pid)

theorem peer_put (pid : Option PeerId) : Preserves Inv (peerPut pid) := ReadyCiphertext.peer_put pid

theorem publication_middle (pid : PeerId) (id : SkbId) (state : PacketState) :
    Preserves Inv (publicationMiddle pid id state) := by
  apply occurrence_passive
  · intro initial
    change Preserves (fun w => txCryptWire w = initial) _
    unfold publicationMiddle
    simp only [invariant]
    repeat' first
      | (rx_retention_head setRxSkb; exact (set_rx_wire _ _).wp (· = initial))
      | crypt_wire_step initial
  · exact ownership_queues (rx_publication_middle_ownership pid id state)

theorem publish (id : SkbId) (state : PacketState) :
    Preserves Inv (enqueuePerPeerRx (pure () : WG.M Unit) id state) := by
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
    Preserves Inv (consumeData msg src ds) := by
  have index := index_lookup
  have getKey (id : Option KeypairId) := occurrence_passive
    (keyGet_cryptWire id) (keyGet_tx_queues id)
  have putKey (id : Option KeypairId) (now : Bool) := occurrence_passive
    ((TxRing.keypairPut_frame id now).product (TxDisposition.keyPut_packets id now))
    ((keypairPut_protect id now).factor (fun s => s.2.2.1))
  have allocate (pkt : RxPacket) := occurrence_passive
    (new_rx_wire pkt) (skb_queues _)
  have free (id : SkbId) := occurrence_passive
    (free_rx_wire id) (skb_queues _)
  have enqueue := enqueue
  have publish := publish
  have pay := peer_put
  have peer (pid : PeerId) := getPeer_preserves pid Inv
  have ambient {α : Type} (a : AmbientM α) : Preserves Inv (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [consumeData,WG.orM,keypairGetNull,branch,invariant]
    using [index,getKey,putKey,allocate,free,enqueue,publish,pay,peer,ambient]

theorem modify (f : Device → Device) (epoch : ∀ d, (f d).ifindex = d.ifindex)
    (ring : ∀ d, (f d).encryptQueue = d.encryptQueue)
    (packets : ∀ d, (f d).txSkbs = d.txSkbs) (peers : ∀ d, (f d).peers = d.peers) :
    Preserves Inv (modifyDev f) := by
  apply occurrence_passive
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    cases run
    simp [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,
      Option.map_map,Option.bind_map,Function.comp_def,epoch,ring,packets]
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    cases run
    funext pid
    simp [handoffTxView,Option.bind_map,Function.comp_def,peers]

theorem cpu_next : Preserves Inv cpumaskNextOnline := by
  have device := store  getDev_sameWGStore
  have cpu (number : Int) : Preserves Inv
      (modifyDev fun d => {d with handshakeLastCpu := number}) :=
    modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have ambient {α : Type} (a : AmbientM α) : Preserves Inv (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [cpumaskNextOnline,branch] using [device,cpu,ambient]

theorem packet (msg : List UInt8) (src : SkbSource) :
    Preserves Inv (packetReceive msg src) := by
  have header := store  ((prepareSkbHeader_sameWGWorld msg).factor wgStoreView)
  have ds (protocol : Nat) (bytes : List UInt8) :=
    store  ((ipTunnelGetDsfield_sameWGWorld protocol bytes).factor wgStoreView)
  have device := store  getDev_sameWGStore
  have append : Preserves Inv
      (modifyDev fun d => {d with handshakeQueue := d.handshakeQueue.produce (msg,src), handshakeQueueLen := d.handshakeQueueLen + 1}) :=
    modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have data := consume  msg src
  have cpu := cpu_next
  have ambient {α : Type} (a : AmbientM α) : Preserves Inv (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [packetReceive,branch,invariant,unsupported,queueDeviceWork]
    using [header,ds,device,append,data,cpu,ambient]

theorem receive (msg : List UInt8) (src : SkbSource) :
    Preserves Inv (wgReceive msg src) := by
  have packet := packet  msg src
  have ambient {α : Type} (a : AmbientM α) : Preserves Inv (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [wgReceive,branch,unsupported] using [packet,ambient]


theorem coherent (msg : List UInt8) (src : SkbSource) :
    Preserves (Coherent locals active) (wgReceive msg src) :=
  Native.coherent_join
    (RxPollOccurrences.join (ReceiveIngressCall.erases (.udp msg src))
      (ReceiveIngressCall.allocation (.udp msg src)) (ReceiveOccurrences.receive msg src))
    (receive msg src)

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Receive
