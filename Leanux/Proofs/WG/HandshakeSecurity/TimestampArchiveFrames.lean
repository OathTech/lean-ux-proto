import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveConsumer

/-! Native archive frames. Timestamp writes and peer allocation have their own
contracts; these helpers only retain or delete existing peer incarnations. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins
open ConfiguredReceive
set_option maxHeartbeats 800000

theorem frame (history : List TimestampReceipt) (action : WG.M α)
    (freshness : Freshness.Frame action) (counter : PeerCounter.Same action) :
    Framing.Preserves (StateInv history) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact state_retained hi
    ((hoare_iff_run_ambient _ _ _).mp (freshness w) w a result v b (.refl w) run)
    (by rw [(ProjectedAction.iff_run_ambient _ _ _).mp counter w a result v b run]; exact Nat.le_refl _)

theorem frame_store (history : List TimestampReceipt) (action : WG.M α) (same : SameWGStore action) :
    Framing.Preserves (StateInv history) action :=
  frame history action (Freshness.store action same) (same.factor WGStoreView.peerCounter)

theorem frame_world (history : List TimestampReceipt) (action : WG.M α) (same : SameView id action) :
    Framing.Preserves (StateInv history) action :=
  frame history action (Freshness.world action same) (same.factor WGWorld.peerCounter)

theorem read_peer (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  rw [(getPeer_normal pid w v p a b run).1]
  exact hi

theorem update_peer (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).latestTimestamp = p.latestTimestamp)
    (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (getPeer pid >>= fun p => setPeer pid (f p)) :=
  frame history _ (Freshness.update_peer pid f same) (PeerCounter.update pid f)

theorem update_peer_bind (pid : PeerId) (f : Peer → Peer) (next : Unit → WG.M α)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).latestTimestamp = p.latestTimestamp)
    (history : List TimestampReceipt)
    (tail : ∀ x, Framing.Preserves (StateInv history) (next x)) :
    Framing.Preserves (StateInv history) (getPeer pid >>= fun p => setPeer pid (f p) >>= next) := by
  simpa only [bind_assoc] using preserves_bind (update_peer pid f same history) tail

theorem modify_device (f : Device → Device) (same : ∀ d, (f d).peers = d.peers)
    (history : List TimestampReceipt) : Framing.Preserves (StateInv history) (modifyDev f) := by
  apply frame history _ (Freshness.modify_device f same)
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  rfl

theorem modify_world (f : WGWorld → WGWorld)
    (same : ∀ w, freshnessAt (f w) = freshnessAt w)
    (counter : ∀ w, (f w).peerCounter = w.peerCounter) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (modify f : WG.M Unit) := by
  apply frame history _ (Freshness.modify_world f same)
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  exact counter w

theorem read_key (kid : KeypairId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a key v b hi run
  rw [(KeyTimes.getKeypair_return kid w v key a b run).1]
  exact hi

theorem write_key (kid : KeypairId) (key : Keypair) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (setKeypair kid key) :=
  modify_device (fun d => {d with keypairs := d.keypairs.insert kid key}) (fun _ => rfl) history

theorem index (action : IndexM α) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (liftIndex action) := by
  apply frame history _ (Freshness.index action)
  intro initial
  apply hoare_liftIndex
  exact fun _ _ _ hi _ => hi

theorem skb (action : SkbM α) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (liftSkb action) := by
  apply frame history _ (Freshness.skb action)
  intro initial
  apply hoare_liftSkb
  exact fun _ _ _ hi _ => hi

theorem peer_put (peer : Option PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (peerPut peer) :=
  frame history _ (Freshness.peer_put peer) (PeerCounter.peer_put peer)

theorem maybe_peer (peer : Option PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (peerGetMaybeZero peer) :=
  frame history _ (Freshness.maybe_peer peer) (PeerCounter.maybe_peer peer)

macro "archive_native_step " history:term : tactic => `(tactic| first
  | (receive_update_head Bind.bind
     apply update_peer_bind
     · intro p; exact ⟨rfl,rfl⟩
     intro x)
  | (receive_update_head setPeer; apply update_peer; intro p; exact ⟨rfl,rfl⟩)
  | (rx_retention_head getPeer; exact read_peer _ $history)
  | (rx_retention_head getKeypair; exact read_key _ $history)
  | (rx_retention_head setKeypair; exact write_key _ _ $history)
  | (rx_retention_head get; exact hoare_consequence (hoare_get (StateInv $history)) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head modify; apply modify_world; all_goals (intro w; rfl))
  | (rx_retention_head getDev; exact frame_store $history _ getDev_sameWGStore)
  | (rx_retention_head modifyDev; apply modify_device; intro d; rfl)
  | (rx_retention_head liftIndex; exact index _ $history)
  | (rx_retention_head liftSkb; exact skb _ $history)
  | (rx_retention_head peerPut; exact peer_put _ $history)
  | (rx_retention_head peerGetMaybeZero; exact maybe_peer _ $history)
  | (rx_retention_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ (StateInv $history))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ (StateInv $history))
  | (allocation_release_lift_from IndexM; exact index _ $history)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi run
     cases run)
  | rx_retention_step)

theorem key_get (kid : Option KeypairId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (keypairGet kid) := by
  unfold keypairGet
  simp (config := {zeta := false}) only [refcountIncNotZero,branch,branchCmp,unsupported,invariant]
  repeat' archive_native_step history

theorem key_put (kid : Option KeypairId) (now : Bool) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (keypairPut kid now) := by
  unfold keypairPut
  simp (config := {zeta := false}) only [refcountDecAndTest,branch,branchCmp,unsupported,invariant]
  repeat' archive_native_step history

theorem owner_write (owner : IndexOwner) (peer : Option PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (owner.setPeerWord peer) := by
  cases owner with
  | handshake pid =>
    exact update_peer pid (fun p => {p with handshakeEntryPeer := peer}) (fun _ => ⟨rfl,rfl⟩) history
  | keypair kid =>
    change Framing.Preserves (StateInv history) (getKeypair kid >>= _)
    apply preserves_bind (read_key kid history)
    intro key
    exact write_key kid _ history

theorem acquire_owner (owner : IndexOwner) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (Affiliation.acquireOwner owner) := by
  unfold Affiliation.acquireOwner
  repeat' first
    | (rx_retention_head IndexOwner.setPeerWord; exact owner_write _ _ history)
    | archive_native_step history

theorem lookup (kinds : List IndexKind) (number : Nat) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (indexLookup kinds number) := by
  rw [← Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head Affiliation.acquireOwner; exact acquire_owner _ history)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (StateInv history)
       intro x b
       change Framing.Preserves (StateInv history) _)
    | archive_native_step history

theorem read_saved (pid : PeerId) (history : List TimestampReceipt) :
    Hoare (getPeer pid) (StateInv history)
      (fun p w => StateInv history w ∧ Responder.SavedNativePeer pid p w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  obtain ⟨rfl,rfl,d,device,peer⟩ := getPeer_normal pid w v p a b run
  exact ⟨hi,d,device,peer⟩

theorem write_saved (pid : PeerId) (p : Peer) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).latestTimestamp = p.latestTimestamp)
    (history : List TimestampReceipt) :
    Hoare (setPeer pid (f p))
      (fun w => StateInv history w ∧ Responder.SavedNativePeer pid p w)
      (fun _ => StateInv history) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  obtain ⟨d,device,peer⟩ := hi.2
  have getter : ((getPeer pid).run w).run a = .ok ((p,w),a) := by
    simp [getPeer,getDev,device,peer]
  have whole : (((getPeer pid >>= fun p => setPeer pid (f p)) : WG.M Unit).run w).run a =
      .ok ((result,v),b) := by
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨p,w,a,getter,run⟩
  exact (hoare_iff_run_ambient _ _ _).mp (update_peer pid f same history) _ _ _ _ _ hi.1 whole

theorem write_cell (pid : PeerId) (p q : Peer)
    (same : (q.internalId,q.latestTimestamp) = (p.internalId,p.latestTimestamp))
    (history : List TimestampReceipt) :
    Hoare (setPeer pid q) (fun w => StateInv history w ∧ Responder.SavedNativePeer pid p w)
      (fun _ => StateInv history) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  obtain ⟨d,device,peer⟩ := hi.2
  have equal : freshnessAt v = freshnessAt w :=
    (hoare_iff_run_ambient _ _ _).mp
      (Freshness.write_saved (fun value => value = freshnessAt w) pid q) _ _ _ _ _
      ⟨rfl,by simp [freshnessAt,device,peer,same]⟩ run
  apply state_retained hi.1 (fun pid stamp found => by rw [← equal]; exact found)
  cases run
  exact Nat.le_refl _

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
