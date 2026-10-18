import Leanux.Proofs.WG.TransmitSecurity.NonceNapi
import Leanux.Proofs.WG.TransmitSecurity.EncryptFrames
import Leanux.Proofs.WG.Queues.RxWorkerCuts
import Leanux.Proofs.WG.Packets.PublicationPoll

/-! Worker operations other than callback-driven staging do not allocate
sending nonces. Disposing a batch may remove its final resident key cell. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem send_skb (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    SameView view (sendSkbToPeer pid bytes ds) :=
  full (Origins.Retaining.sendSkbToPeer_material pid bytes ds)
    (Keypairs.WGMore.sendSkbToPeer_sameSnapshot pid bytes ds)

theorem data_sent (pid : PeerId) : SameView view (timersDataSent pid) :=
  full (Origins.Retaining.timersDataSent_material pid)
    (Keypairs.WGTransitions.timersDataSent_sameSnapshot pid)

theorem fresh_tx (pid : PeerId) : SameView view (keepKeyFresh pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact (queuedHandshake _ _).wp (fun s => s = initial))
    | (rx_retention_head branchExpired; exact ((branchExpired_sameWGWorld _ _ _ _).factor view).wp (fun s => s = initial))
    | nonce_frame_step initial

theorem data_done (pid : PeerId) (item : List SkbId) : SameView view (createDataDone pid item) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold createDataDone WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head timersTraversal; exact (traversal _).wp (fun s => s = initial))
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact (sent _).wp (fun s => s = initial))
    | (rx_retention_head timersDataSent; exact (data_sent _).wp (fun s => s = initial))
    | (rx_retention_head sendSkbToPeer; exact (send_skb _ _ _).wp (fun s => s = initial))
    | (rx_retention_head keepKeyFresh; exact (fresh_tx _).wp (fun s => s = initial))
    | (rx_retention_head getTxSkb; exact (packet_read _).wp (fun s => s = initial))
    | (rx_retention_head ForIn.forIn; apply loop; intro x b)
    | nonce_frame_step initial

theorem tx_step (pid : PeerId) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (txStep pid) := by
  unfold txStep WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head createDataDone; exact native_frame h (data_done _ _))
    | nonce_poll_native_step h

theorem encrypt (slot : KeypairId) (pkt : DataPacket) :
    SameView (fun w : World => view w.wg) (encryptPacket Env.checksumHelp slot pkt) := by
  intro initial
  let P := fun w : World => view w.wg = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have checksum (p : Packet) : Preserves P (Env.checksumHelp p) :=
    (checksumHelp_sameWorld p).wp P
  have padding : Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    (sameView_liftWG (fun w : World => view w.wg) view _
      ((calculateSkbPadding_sameWGWorld _ _).factor view) (fun _ _ _ same => same)).wp (· = initial)
  have read : Preserves P (monadLift (getKeypair slot) : Leanux.M Keypair) :=
    (sameView_liftWG (fun w : World => view w.wg) view _ (key_read slot) (fun _ _ _ same => same)).wp (· = initial)
  change Preserves P _
  routing_tx_source [encryptPacket] using [padding,checksum,ambient,read]


theorem rx_publish (id : SkbId) (state : PacketState) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (RxWorkers.publishSource id state) := by
  unfold RxWorkers.publishSource
  simp (config := {zeta := false}) only [invariant]
  repeat' first
    | (rx_retention_head setRxSkb; exact native_frame h (skb _))
    | nonce_poll_native_step h

theorem rx_prepare (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head decryptPacket; exact native_frame h (decrypt _))
    | (rx_retention_head setRxSkb; exact native_frame h (skb _))
    | (rx_retention_head RxWorkers.publishSource; exact rx_publish _ _ h)
    | nonce_poll_native_step h

theorem tx_ring : SameView view TxRing.pollSource := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold TxRing.pollSource
  repeat' first
    | (rx_retention_head getDev; exact device_read.wp (fun s => s = initial))
    | nonce_frame_step initial

theorem encrypt_step_tail (item : Option (List SkbId)) (h : List Allocation) :
    Preserves (fun w : World => Inv (view w.wg) h) (RxWorkers.encryptStepTailSource item) := by
  let P := fun w : World => Inv (view w.wg) h
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have packetRead (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    PublicationPoll.native_product _ _ (native_frame h (packet_read id))
  have packetWrite (id : SkbId) (f : DataPacket → DataPacket) : Preserves P
      (monadLift (setTxSkb id f) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (native_frame h (packet_write id f))
  have encryptSpec (slot : KeypairId) (pkt : DataPacket) : Preserves P (encryptPacket Env.checksumHelp slot pkt) :=
    (encrypt slot pkt).wp (fun s => Inv s h)
  have enqueue (item : List SkbId) (state : PacketState) : Preserves P
      (monadLift (enqueuePerPeerTx item state) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (enqueuePeer item state h)
  change Preserves P _
  routing_tx_source [RxWorkers.encryptStepTailSource] using [ambient,packetRead,packetWrite,encryptSpec,enqueue]

theorem product_lift {α : Type} {a : Leanux.M α}
    (safe : ∀ h, Preserves (fun w : World => Inv (view w.wg) h) a) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (liftPrefix a) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.nodup)
  intro h w x v hi hr
  exact (hoare_iff_run _ _ _).mp (safe h) w x v hi hr

theorem product_ambient {α : Type} (a : AmbientM α) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup
      (liftPrefix (monadLift a : Leanux.M α)) :=
  product_lift (fun _ => productAmbient_spec a _ (fun _ _ hi => hi))

theorem product_native {α : Type} {a : WG.M α}
    (safe : ∀ h, Preserves (fun w => Inv (view w) h) a) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (liftPrefix (liftWG a)) :=
  product_lift (fun h => PublicationPoll.native_product _ _ (safe h))

theorem product_frame {α : Type} {a : WG.M α} (frame : SameView view a) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup (liftPrefix (liftWG a)) :=
  product_native (fun h => native_frame h frame)

theorem resched (worker : Worker) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup
      (liftPrefix (Env.condResched worker)) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.nodup)
    product_store (condResched_sameKernel worker)


theorem product_stop {α : Type} (e : Stop) :
    PrefixPreserves (fun h w => Inv (view w.wg) h) List.Nodup
      (liftPrefix (throw e : Leanux.M α)) := by
  apply product_lift
  intro h
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi hr
  cases hr

end Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
