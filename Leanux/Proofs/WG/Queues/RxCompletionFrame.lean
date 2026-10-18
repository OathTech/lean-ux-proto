import Leanux.Proofs.WG.Queues.RxTxFrames

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! The complete original receive-completion call retains every surviving
receive queue. This projection theorem does not assert delivery, ownership,
access-prefix completeness, or a retained World after an exception. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem lookup_rxQueues (root : Option NodeId) (bits key : Nat) :
    SameView rxQueues (lookup root bits key) := by
  have ambient {α : Type} (action : AmbientM α) :
      SameView rxQueues (MonadLift.monadLift action : WG.M α) :=
    fun s => hoare_liftAmbient action (fun w => rxQueues w = s)
  have aip {α : Type} (action : AipM α) :
      SameView rxQueues (MonadLift.monadLift action : WG.M α) := by
    intro s
    apply hoare_liftAip action
    intro w d store hi hd
    unfold rxQueues at hi ⊢
    simpa only [hd, Option.bind_some] using hi
  have endian : SameView rxQueues (swapEndian bits) := by
    unfold swapEndian
    apply SameView.bind (ambient _)
    intro yes
    cases yes
    · exact SameView.bind (ambient _) (fun _ => SameView.pure _ _)
    · exact SameView.pure _ _
  unfold lookup
  apply SameView.bind endian
  intro _
  apply SameView.bind (aip _)
  intro node
  apply SameView.bind (ambient _)
  intro found
  cases found <;> dsimp only
  · exact SameView.pure _ _
  · cases node with
    | none => exact SameView.bind (ambient _) (fun _ => SameView.pure _ _)
    | some id =>
      apply SameView.bind (aip _)
      intro n
      apply SameView.bind (peerGetMaybeZero_rxQueues n.peer)
      intro peer
      apply SameView.bind (ambient _)
      intro gone
      cases gone
      · exact SameView.pure _ _
      · exact SameView.bind (ambient _) (fun _ => SameView.pure _ _)

theorem lookupSrc_rxQueues (protocol : Nat) (bytes : List UInt8) :
    SameView rxQueues (lookupSrc protocol bytes) := by
  have ambient {α : Type} (action : AmbientM α) :
      SameView rxQueues (MonadLift.monadLift action : WG.M α) :=
    fun s => hoare_liftAmbient action (fun w => rxQueues w = s)
  unfold lookupSrc
  apply SameView.bind (rxQueues_kernel (project := id) getDev_sameWGStore)
  intro d
  dsimp only
  apply SameView.bind (ambient _)
  intro ipv4
  cases ipv4
  · apply SameView.bind (ambient _)
    intro ipv6
    cases ipv6
    · exact SameView.pure _ _
    · exact lookup_rxQueues _ _ _
  · exact lookup_rxQueues _ _ _

theorem dishonest_rxQueues (why : Dishonest) : SameView rxQueues (dishonest why) :=
  modifyDev_rxQueues _ (fun d => by cases why <;> rfl) (fun d => by cases why <;> rfl)

theorem updateRxStats_rxQueues (pid : PeerId) (len : Nat) :
    SameView rxQueues (updateRxStats pid len) := by
  unfold updateRxStats
  apply SameView.bind (modifyDev_rxQueues
    (fun d => { d with rxPackets := d.rxPackets + 1, rxBytes := d.rxBytes + len })
    (fun _ => rfl) (fun _ => rfl))
  intro _
  exact modifyPeer_rxQueues pid (fun p => {p with rxBytes := p.rxBytes + len})
    (fun _ => rfl) (fun _ => rfl)

theorem consumeDataDone_rxQueues (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    RetainsRx (consumeDataDone pid pkt endpoint) := by
  apply ProjectedAction.of_wp
  intro s
  let P := fun w : WGWorld => ResidentsRetained s (rxQueues w)
  have ambient {α : Type} (action : AmbientM α) :
      Preserves P (MonadLift.monadLift action : WG.M α) := hoare_liftAmbient action P
  have choice {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
      (hy : p → Preserves P yes) (hn : ¬p → Preserves P no) :
      Preserves P (if p then yes else no) := by
    by_cases h : p
    · simpa only [ite_eq_left h] using hy h
    · simpa only [ite_eq_right h] using hn h
  have ce4 (bytes : List UInt8) : Preserves P (ipEcnSetCe bytes) := by
    unfold ipEcnSetCe branch
    apply preserves_bind (ambient _)
    intro b
    cases b <;> exact preserves_pure _
  have ect4 (bytes : List UInt8) : Preserves P (ipEcnSetEct1 bytes) := by
    unfold ipEcnSetEct1 branch
    apply preserves_bind (ambient _)
    intro b
    cases b <;> exact preserves_pure _
  have ce6 (bytes : List UInt8) : Preserves P (ip6EcnSetCe bytes) := by
    unfold ip6EcnSetCe branch
    apply preserves_bind (ambient _)
    intro b
    cases b <;> exact preserves_pure _
  have ect6 (bytes : List UInt8) : Preserves P (ip6EcnSetEct1 bytes) := by
    unfold ip6EcnSetEct1 branch
    apply preserves_bind (ambient _)
    intro b
    cases b <;> exact preserves_pure _
  have ecnSet (ce : Bool) (protocol : Nat) (bytes : List UInt8) :
      Preserves P (inetEcnSet ce protocol bytes) := by
    unfold inetEcnSet branch invariant
    repeat' first
      | (rx_retention_head ipEcnSetCe; exact ce4 _)
      | (rx_retention_head ipEcnSetEct1; exact ect4 _)
      | (rx_retention_head ip6EcnSetCe; exact ce6 _)
      | (rx_retention_head ip6EcnSetEct1; exact ect6 _)
      | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
      | (rx_retention_head MonadLift.monadLift; exact ambient _)
      | (rx_retention_head ite; apply choice; intro)
      | rx_retention_step
  have hecn (protocol outer : Nat) (bytes : List UInt8) :
      Preserves P (inetEcnDecapsulate protocol outer bytes) := by
    unfold inetEcnDecapsulate branch
    repeat' first
      | (rx_retention_head inetEcnSet; exact ecnSet _ _ _)
      | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
      | (rx_retention_head MonadLift.monadLift; exact ambient _)
      | (rx_retention_head ite; apply choice; intro)
      | rx_retention_step
  have preserve : Preserves P (consumeDataDone pid pkt endpoint) := by
    unfold consumeDataDone WG.andM WG.orM branch
    repeat' first
      | (rx_retention_head setPeerEndpoint; exact (setPeerEndpoint_rxQueues _ _).wp (ResidentsRetained s))
      | (rx_retention_head receivedWithKeypair; exact (receivedWithKeypair_rxQueues _ _).wp (ResidentsRetained s))
      | (rx_retention_head timersHandshakeComplete; exact (timersHandshakeComplete_rxQueues _ _).wp (ResidentsRetained s))
      | (rx_retention_head sendStagedPackets; exact RetainsRx.wp (sendStagedPackets_rxQueues _) s)
      | (rx_retention_head keepKeyFreshRx; exact RetainsRx.wp (keepKeyFreshRx_rxQueues _) s)
      | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact (timersAnyAuthenticatedPacketReceived_rxQueues _).wp (ResidentsRetained s))
      | (rx_retention_head timersTraversal; exact (timersTraversal_rxQueues _).wp (ResidentsRetained s))
      | (rx_retention_head timersDataReceived; exact (timersDataReceived_rxQueues _).wp (ResidentsRetained s))
      | (rx_retention_head updateRxStats; exact (updateRxStats_rxQueues _ _).wp (ResidentsRetained s))
      | (rx_retention_head dishonest; exact (dishonest_rxQueues _).wp (ResidentsRetained s))
      | (rx_retention_head inetEcnDecapsulate; exact hecn _ _ _)
      | (rx_retention_head lookupSrc; exact (lookupSrc_rxQueues _ _).wp (ResidentsRetained s))
      | (rx_retention_head peerPut; exact RetainsRx.wp (peerPut_rxQueues _) s)
      | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
      | (rx_retention_head MonadLift.monadLift; exact ambient _)
      | (rx_retention_head ite; apply choice; intro)
      | rx_retention_step
  apply hoare_consequence preserve
  · intro w hw
    dsimp only [P]
    rw [hw]
    exact rx_retained_refl _
  · exact fun _ _ h => h

end Leanux.Proofs.WG.Queues
