import Leanux.Proofs.WG.TransmitSecurity.StagedReleaseFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverHandshakeFrames

/-! Staged-queue/peer-allocation frames for the actual native helpers. Deleting
reference releases retain the ordered plaintexts of every surviving peer; their frames
do not assert that the peer itself remains resident. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

abbrev Frame (action : WG.M α) := ∀ initial, Framing.Preserves (Retains initial) action

theorem of_run (action : WG.M α)
    (frame : ∀ w a x v b, (action.run w).run a = .ok ((x,v),b) → Retains w v) :
    Frame action := by
  intro initial
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact hi.trans (frame w a x v b run)

theorem of_view (action : WG.M α) (same : SameView stagedAt action) : Frame action := by
  apply of_run
  intro w a x v b run pid cell found
  rw [← (ProjectedAction.iff_run_ambient _ _ _).mp same w a x v b run]
  exact found

theorem store (action : WG.M α) (same : SameWGStore action) : Frame action :=
  of_view action (same.of_factor
    (fun s : WGStoreView => fun pid => (s.dev.bind fun d => d.peers[pid]?).map
      fun p => (p.internalId,p.staged)) stagedAt (fun _ => rfl))

theorem world (action : WG.M α) (same : SameView id action) : Frame action :=
  of_view action (same.factor stagedAt)

theorem read_peer (pid : PeerId) : Frame (getPeer pid) := by
  apply of_run
  intro w a p v b run
  rw [(getPeer_normal pid w v p a b run).1]
  exact .refl _

theorem read_saved (P : (PeerId → Option (Nat × List Packet)) → Prop) (pid : PeerId) :
    Hoare (getPeer pid) (fun w => P (stagedAt w))
      (fun p w => P (stagedAt w) ∧ stagedAt w pid = some (p.internalId,p.staged)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  obtain ⟨rfl,_,d,hd,hp⟩ := getPeer_normal pid w v p a b run
  exact ⟨hi,by simp [stagedAt,hd,hp]⟩

theorem write_saved (P : (PeerId → Option (Nat × List Packet)) → Prop)
    (pid : PeerId) (p : Peer) :
    Hoare (setPeer pid p)
      (fun w => P (stagedAt w) ∧ stagedAt w pid = some (p.internalId,p.staged))
      (fun _ w => P (stagedAt w)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases run
  suffices same : stagedAt {w with dev := w.dev.map fun d => {d with peers := d.peers.insert pid p}} = stagedAt w by
    exact same ▸ hi.1
  funext q
  cases hd : w.dev with
  | none => simp [stagedAt,hd]
  | some d =>
    by_cases eq : pid = q
    · subst q
      simpa [stagedAt,hd] using hi.2.symm
    · simp [stagedAt,hd,Std.TreeMap.getElem?_insert,eq]

theorem update_peer (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged) :
    Frame (getPeer pid >>= fun p => setPeer pid (f p)) :=
  of_run _ (fun w a x v b run => modifyPeer_staged pid f same w v a b x run)

theorem update_peer_bind (pid : PeerId) (f : Peer → Peer) (next : Unit → WG.M α)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged)
    (initial : WGWorld) (tail : ∀ x, Framing.Preserves (Retains initial) (next x)) :
    Framing.Preserves (Retains initial)
      (getPeer pid >>= fun p => setPeer pid (f p) >>= next) := by
  simpa only [bind_assoc] using preserves_bind (update_peer pid f same initial) tail

theorem modify_device (f : Device → Device) (same : ∀ d, (f d).peers = d.peers) :
    Frame (modifyDev f) := by
  apply of_view
  intro initial
  apply hoare_modify
  intro w hi
  rw [← hi]
  funext pid
  change ((w.dev.map f).bind fun d => d.peers[pid]?).map (fun p => (p.internalId,p.staged)) = _
  simp only [Option.bind_map,Function.comp_def,same]
  rfl

theorem modify_world (f : WGWorld → WGWorld) (same : ∀ w, stagedAt (f w) = stagedAt w) :
    Frame (modify f) := by
  apply of_view
  intro initial
  apply hoare_modify
  intro w hi
  simpa only [same] using hi

theorem read_key (kid : KeypairId) : Frame (getKeypair kid) := by
  apply of_run
  intro w a key v b run
  rw [(KeyTimes.getKeypair_return kid w v key a b run).1]
  exact .refl _

theorem write_key (kid : KeypairId) (key : Keypair) : Frame (setKeypair kid key) :=
  modify_device _ (fun _ => rfl)

theorem index (action : IndexM α) : Frame (liftIndex action) := by
  intro initial
  apply hoare_liftIndex
  intro w d table hi hd
  intro pid cell found
  apply hi pid cell
  simpa only [stagedAt,hd,Option.bind_some] using found

theorem skb (action : SkbM α) : Frame (liftSkb action) := by
  intro initial
  apply hoare_liftSkb
  intro w d packets hi hd
  intro pid cell found
  apply hi pid cell
  simpa only [stagedAt,hd,Option.bind_some] using found

theorem peer_put (peer : Option PeerId) : Frame (peerPut peer) :=
  of_run _ (fun w a x v b run => peerPut_retains peer w v a b x run)

theorem maybe_peer (peer : Option PeerId) : Frame (peerGetMaybeZero peer) :=
  of_run _ (fun w a x v b run => peerGetMaybeZero_retains peer w v a b x run)

macro "staged_native_step " initial:term : tactic => `(tactic| first
  | (receive_update_head Bind.bind
     apply update_peer_bind
     · intro p; exact ⟨rfl,rfl⟩
     intro x)
  | (receive_update_head setPeer; apply update_peer; intro p; exact ⟨rfl,rfl⟩)
  | (rx_retention_head getPeer; exact read_peer _ $initial)
  | (rx_retention_head getKeypair; exact read_key _ $initial)
  | (rx_retention_head setKeypair; exact write_key _ _ $initial)
  | (rx_retention_head get; exact hoare_consequence (hoare_get (Retains $initial)) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head modify; apply modify_world; intro w; rfl)
  | (rx_retention_head getDev; exact store _ getDev_sameWGStore $initial)
  | (rx_retention_head modifyDev; apply modify_device; intro d; rfl)
  | (rx_retention_head liftIndex; exact index _ $initial)
  | (rx_retention_head liftSkb; exact skb _ $initial)
  | (rx_retention_head peerPut; exact peer_put _ $initial)
  | (rx_retention_head peerGetMaybeZero; exact maybe_peer _ $initial)
  | (rx_retention_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ (Retains $initial))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ (Retains $initial))
  | (allocation_release_lift_from IndexM; exact index _ $initial)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi run
     cases run)
  | rx_retention_step)

theorem key_get (kid : Option KeypairId) : Frame (keypairGet kid) := by
  intro initial
  unfold keypairGet
  simp (config := {zeta := false}) only [refcountIncNotZero,branch,branchCmp,unsupported,invariant]
  repeat' staged_native_step initial

theorem key_put (kid : Option KeypairId) (now : Bool) : Frame (keypairPut kid now) := by
  intro initial
  unfold keypairPut
  simp (config := {zeta := false}) only [refcountDecAndTest,branch,branchCmp,unsupported,invariant]
  repeat' staged_native_step initial

theorem owner_write (owner : IndexOwner) (peer : Option PeerId) : Frame (owner.setPeerWord peer) := by
  intro initial
  cases owner with
  | handshake pid =>
    exact update_peer pid (fun p => {p with handshakeEntryPeer := peer}) (fun _ => ⟨rfl,rfl⟩) initial
  | keypair kid =>
    change Framing.Preserves (Retains initial) (getKeypair kid >>= _)
    apply preserves_bind (read_key kid initial)
    intro key
    exact write_key kid _ initial

theorem acquire_owner (owner : IndexOwner) : Frame (Affiliation.acquireOwner owner) := by
  intro initial
  unfold Affiliation.acquireOwner
  repeat' first
    | (rx_retention_head IndexOwner.setPeerWord; exact owner_write _ _ initial)
    | staged_native_step initial

theorem lookup (kinds : List IndexKind) (number : Nat) : Frame (indexLookup kinds number) := by
  intro initial
  rw [← Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head Affiliation.acquireOwner; exact acquire_owner _ initial)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Retains initial)
       intro x b
       change Framing.Preserves (Retains initial) _)
    | staged_native_step initial

end Leanux.Proofs.WG.TransmitSecurity.Staged
