import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchivePoll

namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Packets

theorem lookup_dst (family addr : Nat) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (lookupDst family addr) := by
  unfold lookupDst
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.lookup; exact route_lookup _ _ _ history)
    | archive_timer_step history

theorem trim (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (xmitTrim pid) := by
  unfold xmitTrim
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply preserves_bind (read_peer pid history)
  intro original
  apply preserves_bind
  · apply list_view_spec id (StateInv history)
    intro index state
    apply hoare_bind _ _ (read_saved pid history)
    intro p
    apply hoare_bind _ _ (hoare_liftAmbient
      (AmbientM.branch .xmitStagedTrimIter (p.staged.length > MAX_STAGED_PACKETS)) _)
    intro take
    split
    · apply hoare_bind _ _ (write_saved pid p (fun p => {p with staged := p.staged.drop 1})
        (fun _ => ⟨rfl,rfl⟩) history)
      intro _
      change Framing.Preserves (StateInv history) _
      repeat' archive_timer_step history
    · exact hoare_consequence (preserves_pure _) (fun _ hi => hi.1) (fun _ _ hi => hi)
  · intro _; exact preserves_pure _

theorem splice (pid : PeerId) (packets : List Packet) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (xmitSplice pid packets) := by
  unfold xmitSplice
  rw [getPeer_twice]
  exact update_peer pid (fun p => {p with staged := p.staged ++ packets}) (fun _ => ⟨rfl,rfl⟩) history

theorem tx_front (family addr : Nat) (packets : List Packet) (mtu : Nat)
    (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (txFront family addr packets mtu) := by
  unfold txFront txCheck txSelect txError txHeaders txWalk WG.andM
  simp (config := {zeta := false}) only [branch,invariant,skipCutSites,envOk]
  repeat' first
    | rxstack_preserves_join
    | (rx_retention_head lookupDst; exact lookup_dst _ _ history)
    | (rx_retention_head xmitTrim; exact trim _ history)
    | (rx_retention_head xmitSplice; exact splice _ _ history)
    | (rx_retention_head loopbackSend; exact frame_store history _ (loopbackSend_kernel _ _))
    | (allocation_release_lift_from Net.M; exact frame_store history _ (liftRouting_sameWGStore _))
    | archive_poll_step history

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
