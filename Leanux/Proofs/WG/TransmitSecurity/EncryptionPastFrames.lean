import Leanux.Proofs.WG.TransmitSecurity.EncryptionPast

/-! Native projection frames for historical encryption exclusion. These facts
mention only the device epoch, allocation frontier and live encryption ring. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity
set_option maxHeartbeats 600000

private def fromParts (parts : AllocationMetadata × Option (Nat × PtrRing (List SkbId))) : View :=
  ⟨parts.1.nextEpoch,parts.1.device.map fun d =>
    ⟨d.epoch,d.nextPacket,(parts.2.map (fun pair => pair.2.items)).getD []⟩⟩

theorem factor (w : WGWorld) : fromParts (allocationMetadata w,TxRing.nativeCell w) = view w := by
  cases device : w.dev <;> simp [fromParts,allocationMetadata,TxRing.nativeCell,view,device,deviceAllocationMetadata]

theorem parts {action : WG.M α} (metadata : SameView allocationMetadata action)
    (ring : SameView TxRing.nativeCell action) : SameView view action :=
  (metadata.product ring).of_factor fromParts view (fun w => (factor w).symm)

theorem store {action : WG.M α} (same : SameWGStore action) : SameView view action :=
  same.of_factor (fun s => view {dev := s.dev,netIfindexNext := s.netIfindexNext}) view (fun _ => rfl)

theorem modify (f : Device → Device)
    (metadata : ∀ d, deviceAllocationMetadata (f d) = deviceAllocationMetadata d)
    (ring : ∀ d, (f d).encryptQueue = d.encryptQueue) : SameView view (modifyDev f) := by
  apply parts (metadata_modifyDev f metadata)
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  cases run
  have epochs : ∀ d, (f d).ifindex = d.ifindex := fun d => congrArg DeviceAllocationMetadata.epoch (metadata d)
  simp only [TxRing.nativeCell,Option.map_map,Function.comp_def,epochs,ring]

theorem read_packet (id : SkbId) : SameView view (getTxSkb id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a packet v b run
  exact congrArg view (Packets.getTxSkb_current id w v packet a b run).1

theorem set_packet (id : SkbId) (f : DataPacket → DataPacket) : SameView view (setTxSkb id f) := by
  apply parts (setTxSkb_metadata id f)
  intro initial
  unfold setTxSkb
  apply hoare_liftSkb
  intro w d entries before device
  simpa only [TxRing.nativeCell,device,Option.map_some] using before

theorem peer_get (id : PeerId) : SameView view (peerGet id) :=
  parts (peerGet_metadata id) (TxRing.peerGet_frame id)

theorem peer_put (id : Option PeerId) : SameView view (peerPut id) :=
  parts (peerPut_metadata id) (TxRing.peerPut_frame id)

macro "encryption_past_frame " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getDev; exact (store getDev_sameWGStore).wp (· = $initial))
  | (rx_retention_head getTxSkb; exact (read_packet _).wp (· = $initial))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (rx_retention_head peerGet; exact (peer_get _).wp (· = $initial))
  | (rx_retention_head peerPut; exact (peer_put _).wp (· = $initial))
  | (rx_retention_head setTxSkb; exact (set_packet _ _).wp (· = $initial))
  | (rx_retention_head setPeer; unfold setPeer)
  | (rx_retention_head modifyDev; apply (modify _ ?_ ?_).wp (· = $initial); all_goals intro d; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head get
     exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head MonadStateOf.get
     exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | rx_retention_step)

theorem publish (items : List SkbId) (state : PacketState) : SameView view (enqueuePerPeerTx items state) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold enqueuePerPeerTx cpumaskChooseOnline
  simp only [Nat.mod_one,Std.Legacy.Range.forIn_eq_forIn_range',
    branch,invariant,peekQueuedUnit,recordQueued]
  repeat' first
    | (rx_retention_head ForIn.forIn; apply list_view_spec id (fun w => view w = initial); intro x b; change Preserves (fun w => view w = initial) _)
    | encryption_past_frame initial

theorem packet (key : KeypairId) (pkt : DataPacket) :
    SameView (fun w : World => view w.wg) (encryptPacket Env.checksumHelp key pkt) :=
  (encrypt_packet_store key pkt).of_factor
    (fun s => view {dev := s.dev,netIfindexNext := s.netIfindexNext})
    (fun w : World => view w.wg) (fun _ => rfl)

theorem native_tail (items : Option (List SkbId)) :
    SameView (fun w : World => view w.wg) (RxWorkers.encryptStepTailSource items) := by
  intro initial
  let P := fun w : World => view w.wg = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have native {α : Type} (a : WG.M α) (same : SameView view a) :
      Preserves P (monadLift a : Leanux.M α) :=
    (sameView_liftWG (fun w : World => view w.wg) view a same
      (fun _ _ _ hi => hi)).wp (· = initial)
  have read := fun id => native (getTxSkb id) (read_packet id)
  have write := fun id f => native (setTxSkb id f) (set_packet id f)
  have publish := fun batch state => native (enqueuePerPeerTx batch state) (publish batch state)
  have crypt (key : KeypairId) (pkt : DataPacket) : Preserves P (encryptPacket Env.checksumHelp key pkt) :=
    (packet key pkt).wp (· = initial)
  change Preserves P _
  routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,publish,crypt,ambient]

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
