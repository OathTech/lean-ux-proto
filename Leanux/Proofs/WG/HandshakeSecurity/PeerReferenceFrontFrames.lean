import Leanux.Proofs.WG.HandshakeSecurity.PeerReferencePoll

/-! Destination selection and native staging-list edits retain positive peers. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Packets

theorem lookup_dst (family addr : Nat) :
    Framing.Preserves Inv (lookupDst family addr) := by
  unfold lookupDst
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.lookup; exact route_lookup _ _ _)
    | peer_reference_timer_step

theorem trim (pid : PeerId) :
    Framing.Preserves Inv (xmitTrim pid) := by
  unfold xmitTrim
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply preserves_bind (read_peer pid)
  intro original
  apply preserves_bind
  · apply list_view_spec id Inv
    intro index state
    apply hoare_bind _ _ (read_saved pid)
    intro p
    apply hoare_bind _ _ (hoare_liftAmbient
      (AmbientM.branch .xmitStagedTrimIter (p.staged.length > MAX_STAGED_PACKETS)) _)
    intro take
    split
    · apply hoare_bind _ _ (write_saved pid p (fun p => {p with staged := p.staged.drop 1})
        (fun _ => rfl))
      intro _
      change Framing.Preserves Inv _
      repeat' peer_reference_timer_step
    · exact hoare_consequence (preserves_pure _) (fun _ hi => hi.1) (fun _ _ hi => hi)
  · intro _; exact preserves_pure _

theorem splice (pid : PeerId) (packets : List Packet) :
    Framing.Preserves Inv (xmitSplice pid packets) := by
  unfold xmitSplice
  rw [getPeer_twice]
  exact update_peer pid (fun p => {p with staged := p.staged ++ packets}) (fun _ positive => positive)

theorem tx_front (family addr : Nat) (packets : List Packet) (mtu : Nat)
    :
    Framing.Preserves Inv (txFront family addr packets mtu) := by
  unfold txFront txCheck txSelect txError txHeaders txWalk WG.andM
  simp (config := {zeta := false}) only [branch,invariant,skipCutSites,envOk]
  repeat' first
    | rxstack_preserves_join
    | (rx_retention_head lookupDst; exact lookup_dst _ _)
    | (rx_retention_head xmitTrim; exact trim _)
    | (rx_retention_head xmitSplice; exact splice _ _)
    | (rx_retention_head loopbackSend; exact store (loopbackSend_kernel _ _))
    | (allocation_release_lift_from Net.M; exact store (liftRouting_sameWGStore _))
    | peer_reference_poll_step

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
