import Leanux.Proofs.WG.TransmitSecurity.NonceHandshakeFrames
import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationSource

/-! Receiving replay state is separate from the sending nonce frontier.
These frames use the original key read/write relationship, with no bitmap-shape
premise and no supposition that a rejected receive leaves all key fields intact. -/
set_option maxHeartbeats 600000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem read_cell (id : KeypairId) (P : View → Prop) :
    Hoare (getKeypair id) (fun w => P (view w))
      (fun k w => P (view w) ∧ (view w).cells id = some (Nonce.cell k)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a k v b hi hr
  obtain ⟨rfl,_,d,hd,hk⟩ := KeyTimes.getKeypair_return id w v k a b hr
  exact ⟨hi,by simp [view,hd,hk]⟩

theorem write_cell (id : KeypairId) (k : Keypair) (P : View → Prop) :
    Preserves (fun w => P (view w) ∧ (view w).cells id = some (Nonce.cell k)) (setKeypair id k) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi hr
  cases hd : w.dev with
  | none => simp [view,hd] at hi
  | some d =>
    cases hr
    have frame : view (CounterWindow.store w id k) = view w := by
      rw [view_store w d id k hd]
      apply View.ext
      · rfl
      · funext other
        by_cases same : other = id
        · subst other
          simpa only [View.put,↓reduceIte] using hi.2.symm
        · simp [View.put,same]
    change P (view (CounterWindow.store w id k)) ∧
      (view (CounterWindow.store w id k)).cells id = some (Nonce.cell k)
    simpa only [frame] using hi

theorem receive_counter (id : KeypairId) (nonce : Nat) : SameView view (counterValidate id nonce) := by
  intro initial
  unfold counterValidate
  apply hoare_bind _ _ (read_cell id (fun s => s = initial))
  intro k
  apply hoare_consequence
    (P := fun w => view w = initial ∧ (view w).cells id = some (Nonce.cell k))
    (Q := fun _ w => view w = initial ∧ (view w).cells id = some (Nonce.cell k))
    ?_ (fun _ h => h) (fun _ _ h => h.1)
  change Preserves (fun w => view w = initial ∧ (view w).cells id = some (Nonce.cell k)) _
  unfold WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head setKeypair; exact write_cell _ _ (fun s => s = initial))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ForIn.forIn; apply loop; intro x b)
    | rx_retention_step


theorem decrypt (pkt : RxPacket) : SameView view (decryptPacket pkt) := by
  rw [KeyTimes.decryptPacket_factor]
  apply SameView.bind (ambient _)
  intro missing
  cases missing with
  | true => exact SameView.pure _ _
  | false =>
    apply SameView.bind (key_read _)
    intro k
    apply SameView.bind ((Origins.receiveReject_sameWGWorld k).factor view)
    intro reject
    cases reject with
    | false => exact (Origins.receiveTail_sameWGWorld pkt k).factor view
    | true =>
      simpa only [bind_assoc, Bool.true_eq, ↓reduceIte, id_eq] using
        (update_key pkt.keypair
          (fun fresh => {fresh with receiving := {fresh.receiving with isValid := false}})
          (fun _ => rfl)).bind (fun _ => SameView.pure view (none : Option RxPacket))

theorem fresh_rx (pid : PeerId) : SameView view (keepKeyFreshRx pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold keepKeyFreshRx WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact (queuedHandshake _ _).wp (fun s => s = initial))
    | (rx_retention_head branchExpired; exact ((branchExpired_sameWGWorld _ _ _ _).factor view).wp (fun s => s = initial))
    | nonce_frame_step initial

theorem data_received (pid : PeerId) : SameView view (timersDataReceived pid) :=
  full (Origins.Retaining.timersDataReceived_material pid)
    (Keypairs.WGTransitions.timersDataReceived_sameSnapshot pid)

theorem dishonest_frame (why : Dishonest) : SameView view (dishonest why) :=
  full (Origins.Retaining.dishonest_material why) (Keypairs.WGMore.dishonest_sameSnapshot why)

theorem rx_stats (pid : PeerId) (len : Nat) : SameView view (updateRxStats pid len) :=
  full (Origins.Retaining.updateRxStats_material pid len)
    (Keypairs.WGMore.updateRxStats_sameSnapshot pid len)

theorem prepare_rest (pid : PeerId) (pkt : RxPacket) : SameView view (RxCredits.prepareRest pid pkt) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold RxCredits.prepareRest WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head keepKeyFreshRx; exact (fresh_rx _).wp (fun s => s = initial))
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact (received _).wp (fun s => s = initial))
    | (rx_retention_head timersTraversal; exact (traversal _).wp (fun s => s = initial))
    | (rx_retention_head timersDataReceived; exact (data_received _).wp (fun s => s = initial))
    | (rx_retention_head dishonest; exact (dishonest_frame _).wp (fun s => s = initial))
    | (rx_retention_head updateRxStats; exact (rx_stats _ _).wp (fun s => s = initial))
    | (rx_retention_head inetEcnDecapsulate; exact (store (inetEcnDecapsulate_sameWGStore _ _ _)).wp (fun s => s = initial))
    | nonce_frame_step initial

theorem lookup_src (protocol : Nat) (bytes : List UInt8) : SameView view (lookupSrc protocol bytes) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupSrc_spec protocol bytes (wgStoreView w)) w a result v b rfl hr
  cases result with
  | none =>
    change wgStoreView v = wgStoreView w at borrowed
    exact congrArg (fun s => View.mk s.keypairCounter
      (fun id => (s.dev.bind fun d => d.keypairs[id]?).map Nonce.cell)) borrowed
  | some pid =>
    obtain ⟨d,p,hd,hp,_,hv⟩ := borrowed
    have dev := congrArg WGStoreView.dev hv
    have frontier := congrArg WGStoreView.keypairCounter hv
    apply View.ext
    · exact frontier
    · funext id
      change v.dev = some _ at dev
      change w.dev = some d at hd
      simp only [view,dev,hd,Option.bind_some]

theorem rx_finish (pid : PeerId) (ready : Packets.RxReady) : SameView view (Packets.rxFinish pid ready) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold Packets.rxFinish Packets.rxAfterLookup
  simp only [branch]
  repeat' first
    | (rx_retention_head lookupSrc; exact (lookup_src _ _).wp (fun s => s = initial))
    | (rx_retention_head WG.peerPut; exact (peerPut _).wp (fun s => s = initial))
    | (rx_retention_head dishonest; exact (dishonest_frame _).wp (fun s => s = initial))
    | (rx_retention_head updateRxStats; exact (rx_stats _ _).wp (fun s => s = initial))
    | nonce_frame_step initial

end Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
