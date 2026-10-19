import Leanux.Proofs.WG.Queues.CurrentSlotFrames

/-! Actual staged-send operations retain three-slot compatibility. The
source may delete keys or peers; no exact-store or liveness premise is used. -/
namespace Leanux.Proofs.WG.CurrentSlots
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
open Lifetimes Queues

private theorem readPeer_spec (pid : PeerId) :
    Hoare (getPeer pid) Inv (fun p w => Inv w ∧
      Affiliation.peerAt w pid = some (Affiliation.peerCell p)) :=
  Affiliation.getPeer_spec (fun v => ∀ s, v = some s → SlotInv s) pid

private theorem writePeer_spec (pid : PeerId) (p : Peer) :
    Hoare (setPeer pid p) (fun w => Inv w ∧
      Affiliation.peerAt w pid = some (Affiliation.peerCell p)) (fun _ => Inv) :=
  Affiliation.setPeer_spec (fun v => ∀ s, v = some s → SlotInv s) pid p

private theorem update_peer (pid : PeerId) (f : Peer → Peer)
    (hf : ∀ p, Affiliation.peerCell (f p) = Affiliation.peerCell p) :
    Preserves Inv (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply hoare_bind _ _ (readPeer_spec pid)
  intro p
  apply hoare_consequence (writePeer_spec pid (f p))
  · intro w h
    exact ⟨h.1,by simpa only [hf] using h.2⟩
  · exact fun _ _ h => h

private theorem update_peer_bind (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (hf : ∀ p, Affiliation.peerCell (f p) = Affiliation.peerCell p)
    (ht : ∀ x, Preserves Inv (tail x)) :
    Preserves Inv (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (update_peer pid f hf) ht

private theorem keyUpdateThen (kid : KeypairId) (f : Keypair → Keypair)
    (hf : ∀ k, Affiliation.keyCell (f k) = Affiliation.keyCell k)
    (next : Keypair → WG.M α) (hn : ∀ k, Preserves Inv (next k)) :
    Preserves Inv (do let k ← getKeypair kid; setKeypair kid (f k); next k) := by
  apply hoare_bind _ _ (Affiliation.getKeypair_spec (fun v => ∀ s, v = some s → SlotInv s) kid)
  intro k
  apply hoare_bind _ _ (hoare_consequence (Affiliation.setKeypair_spec
    (fun v => ∀ s, v = some s → SlotInv s) kid (f k)) ?_ (fun _ _ h => h))
  · intro _; exact hn k
  · intro w h
    exact ⟨h.1,by simpa only [hf] using h.2⟩

private theorem keyUpdate (kid : KeypairId) (f : Keypair → Keypair)
    (hf : ∀ k, Affiliation.keyCell (f k) = Affiliation.keyCell k) :
    Preserves Inv (getKeypair kid >>= fun k => setKeypair kid (f k)) := by
  simpa only [bind_pure_unit] using keyUpdateThen kid f hf (fun _ => pure ()) (fun _ => preserves_pure ())

private theorem getPeer_frame (pid : PeerId) : Preserves Inv (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi hr
  exact (getPeer_normal pid w v p a b hr).1 ▸ hi

private theorem getKeypair_frame (kid : KeypairId) : Preserves Inv (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a k v b hi hr
  exact (KeyTimes.getKeypair_return kid w v k a b hr).1 ▸ hi

macro "slot_traffic_step" : tactic => `(tactic| first
  | (receive_update_head setPeer
     apply update_peer
     intro p; rfl)
  | (receive_update_head Bind.bind
     apply update_peer_bind
     · intro p; rfl
     intro x)
  | (current_key_update_head setKeypair
     apply keyUpdate
     intro k; rfl)
  | (current_key_update_head Bind.bind
     apply keyUpdateThen
     · intro k; rfl
     intro k)
  | (rx_retention_head peerGet; exact fields_preserves (project := fun w => w) (peerGet_fields _))
  | (rx_retention_head peerPut; exact peerPut_preserves _)
  | (rx_retention_head keypairGet; exact keypairGet_preserves _)
  | (rx_retention_head keypairPut; exact keypairPut_preserves _ _)
  | (rx_retention_head getPeer; exact getPeer_frame _)
  | (rx_retention_head getKeypair; exact getKeypair_frame _)
  | (rx_retention_head getDev; unfold getDev)
  | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) Inv)
  | (rx_retention_head get; exact hoare_consequence (hoare_get Inv) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp Inv)
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ Inv)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec (id : WGWorld → WGWorld) Inv
     intro x b
     change Preserves Inv _)
  | (rx_retention_head modifyDev
     apply fields_preserves (project := fun w => w)
     intro initial
     change Preserves (fun w => fields w = initial) _
     slot_fields_step initial)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ Inv)
  | rx_retention_step)

macro "slot_packet_step" : tactic => `(tactic| first
  | (rx_retention_head getTxSkb; unfold getTxSkb)
  | (rx_retention_head setTxSkb; unfold setTxSkb)
  | (rx_retention_head newTxSkb; unfold newTxSkb)
  | (rx_retention_head freeTxSkb; unfold freeTxSkb)
  | (rx_retention_head liftSkb
     apply hoare_liftSkb
     intro w d store hi hd
     apply fields_transport hi
     unfold fields RxCredits.keyWords
     simp only [hd,Option.map_some,Option.bind_some]))

theorem sendQueuedHandshakeInitiation_preserves (pid : PeerId) (retry : Bool) :
    Preserves Inv (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' slot_traffic_step

private theorem choose_fields (pid : PeerId) : SameView fields (cpumaskChooseOnline pid) := by
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold cpumaskChooseOnline
  simp (config := {zeta := false}) only [branch,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec fields (fun s => s = initial)
       intro x b
       change Preserves (fun w => fields w = initial) _)
    | slot_fields_step initial

private theorem enqueueDevice_fields (pid : PeerId) (item : List SkbId) :
    SameView fields (enqueuePerDeviceAndPeer pid item) := by
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold enqueuePerDeviceAndPeer
  simp (config := {zeta := false}) only [branch,setTxSkb,queueDeviceWork,invariant]
  repeat' first
    | (rx_retention_head cpumaskNextOnlineFrom
       exact ((cpumaskNextOnlineFrom_sameStore _).of_factor
         (fun s : WGStoreView => fields {dev := s.dev}) fields (fun _ => rfl)).wp (fun s => s = initial))
    | slot_fields_step initial

private theorem enqueuePeer_preserves (item : List SkbId) (state : PacketState) :
    Preserves Inv (enqueuePerPeerTx item state) := by
  unfold enqueuePerPeerTx
  simp (config := {zeta := false}) only [peekQueuedUnit,recordQueued,invariant]
  repeat' first
    | (rx_retention_head cpumaskChooseOnline
       exact fields_preserves (project := fun w => w) (choose_fields _))
    | slot_packet_step
    | slot_traffic_step

private theorem createData_preserves (pid : PeerId) (item : List SkbId) :
    Preserves Inv (createData pid item) := by
  unfold createData
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer
       exact fields_preserves (project := fun w => w) (enqueueDevice_fields _ _))
    | (rx_retention_head enqueuePerPeerTx; exact enqueuePeer_preserves _ _)
    | slot_packet_step
    | slot_traffic_step

private theorem restoreStaged_preserves (pid : PeerId) (packets : List Packet) :
    Preserves Inv (do setPeer pid { (← getPeer pid) with staged := packets ++ (← getPeer pid).staged }) := by
  apply fields_preserves (project := fun w => w)
  intro initial
  change Preserves (fun w => fields w = initial) _
  repeat' slot_fields_step initial

private theorem stagedOutNokey_preserves (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) :
    Preserves Inv (stagedOutNokey pid packets keypair invalid) := by
  have restore := restoreStaged_preserves pid packets
  have factor : stagedOutNokey pid packets keypair invalid = (do
      if invalid then
        let some id := keypair | invariant "unreachable"
        let k ← getKeypair id
        setKeypair id {k with sending := {k.sending with isValid := false}}
      keypairPut keypair false
      for _ in packets do _ ← branch .stagedOrphanWalk true
      _ ← branch .stagedOrphanWalk false
      (do setPeer pid { (← getPeer pid) with staged := packets ++ (← getPeer pid).staged })
      sendQueuedHandshakeInitiation pid false) := by
    cases invalid <;> cases keypair <;>
      simp only [stagedOutNokey,Bool.false_eq_true,ite_false,ite_true,bind_assoc]
  rw [factor]
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (env_bind_head getPeer; exact restore)
    | (rx_retention_head sendQueuedHandshakeInitiation; exact sendQueuedHandshakeInitiation_preserves _ _)
    | slot_traffic_step

private theorem stagedSubmit_preserves (pid kid : Nat) (packets : List DataPacket) :
    Preserves Inv (RxCredits.stagedSubmit pid kid packets) := by
  unfold RxCredits.stagedSubmit Affiliation.sendAcquire
  repeat' first
    | (rx_retention_head createData; exact createData_preserves _ _)
    | (rx_retention_head List.mapM
       apply mapM_view_spec (id : WGWorld → WGWorld) Inv
       intro packet
       change Preserves Inv _)
    | slot_packet_step
    | slot_traffic_step

private theorem stagedKey_preserves (pid kid : Nat) (packets : List Packet) :
    Preserves Inv (RxCredits.stagedKeySource pid kid packets) := by
  unfold RxCredits.stagedKeySource
  simp (config := {zeta := false}) only [branch,branchCmp]
  repeat' first
    | (rx_retention_head stagedOutNokey; exact stagedOutNokey_preserves _ _ _ _)
    | (rx_retention_head RxCredits.stagedSubmit; exact stagedSubmit_preserves _ _ _)
    | (rx_retention_head ipTunnelEcnEncap; exact (ipTunnelEcnEncap_sameWGWorld _).wp Inv)
    | slot_traffic_step

theorem sendStagedPackets_preserves (pid : PeerId) : Preserves Inv (sendStagedPackets pid) := by
  rw [← RxCredits.stagedFullSource_eq]
  unfold RxCredits.stagedFullSource
  apply hoare_bind _ _ (readPeer_spec pid)
  intro p
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .stagedEmpty p.staged.isEmpty) _)
  intro empty
  cases empty with
  | true => exact hoare_consequence (preserves_pure ()) (fun _ h => h.1) (fun _ _ h => h)
  | false =>
    apply hoare_bind _ _ (writePeer_spec pid {p with staged := []})
    intro _
    change Preserves Inv _
    simp (config := {zeta := false}) only [branch,invariant]
    repeat' first
      | (rx_retention_head stagedOutNokey; exact stagedOutNokey_preserves _ _ _ _)
      | (rx_retention_head RxCredits.stagedKeySource; exact stagedKey_preserves _ _ _)
      | slot_traffic_step

end Leanux.Proofs.WG.CurrentSlots
