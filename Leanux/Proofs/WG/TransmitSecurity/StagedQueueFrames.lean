import Leanux.Proofs.WG.TransmitSecurity.StagedSavedNativeFrames

/-! Handshake scheduling may release a peer, but never introduces plaintext
into a surviving staged queue. The origin frame uses the actual native path. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000

theorem Native.update_peer (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged) :
    Preserves (Inv h) (getPeer pid >>= fun p => setPeer pid (f p)) := by
  apply frame
  · apply SameView.bind
    · exact PacketOrigins.epoch_ring (TxRing.getPeer_frame pid)
    · intro p
      exact PacketOrigins.epoch_ring (TxRing.setPeer_frame pid (f p))
  · exact Staged.update_peer pid f same

theorem Native.update_peer_bind (pid : PeerId) (f : Peer → Peer) (next : Unit → WG.M α)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged)
    (tail : ∀ x, Preserves (Inv h) (next x)) :
    Preserves (Inv h) (getPeer pid >>= fun p => setPeer pid (f p) >>= next) := by
  simpa only [bind_assoc] using preserves_bind (Native.update_peer pid f same) tail

theorem Native.queued (pid : PeerId) (retry : Bool) :
    Preserves (Inv h) (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation
  simp only [branch,peekQueuedUnit,recordQueued]
  repeat' first
    | (receive_update_head Bind.bind
       apply Native.update_peer_bind
       · intro p; exact ⟨rfl,rfl⟩
       intro x)
    | (receive_update_head setPeer; apply Native.update_peer; intro p; exact ⟨rfl,rfl⟩)
    | (rx_retention_head getPeer; exact Native.read_peer _)
    | (rx_retention_head peerGet; exact Native.peer_get _)
    | (rx_retention_head peerPut; exact Native.peer_put _)
    | (rx_retention_head modifyDev; apply Native.modify_device <;> intro d <;> rfl)
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (Inv h))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem queued_appends (pid : PeerId) (retry : Bool) :
    StateAppends (TimerEffects.queuedWith effects pid retry) := by
  have step {α : Type} (a : WG.M α) : StateAppends (effects.step a) := StateAppends.lift a
  have queue (target : PeerId) : StateAppends (effects.append target) := by
    intro w a h
    exact StateAppends.receiptWGObserved (StateAppends.lift _) _ w a h
  unfold TimerEffects.queuedWith
  repeat' first
    | with_reducible exact step _
    | with_reducible exact queue _
    | with_reducible exact StateAppends.pure _
    | with_reducible apply StateAppends.bind
    | split
    | (session_origin_intro_forall; try dsimp only)

theorem queued_observed (pid : PeerId) (retry : Bool) :
    StateSafe (TimerEffects.queuedWith effects pid retry) :=
  state_quiet (queued_appends pid retry)
    (TimerEffects.queued_frame selection?
      (CausalEffects.ops_frames scope? Event.armed Event.queued selection? (fun _ => rfl) (fun _ => rfl)) pid retry)
    (TimerEffects.queued_erases (CausalEffects.ops_erases scope? Event.armed Event.queued) pid retry)
    (fun _ => Native.queued pid retry)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
