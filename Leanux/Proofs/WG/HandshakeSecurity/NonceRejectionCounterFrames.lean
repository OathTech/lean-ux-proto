import Leanux.Proofs.WG.HandshakeSecurity.NonceRejectionReceipts

/-! The native rejection prefix leaves txDropped unchanged through reference
release, orphan traversal and batch restoration. The guarded queue helper starts
only after this prefix has completed. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.NonceRejection
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem edit (f : Device → Device) (same : ∀ d, (f d).txDropped = d.txDropped) :
    SameView dropped (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  cases run
  simp only [dropped,Option.map_map,Function.comp_def,same]

private theorem read_peer (pid : PeerId) : SameView dropped (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  exact congrArg dropped (Origins.getPeer_return pid w v p a b run).1

private theorem read_key (kid : KeypairId) : SameView dropped (getKeypair kid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a key v b run
  exact congrArg dropped (KeyTimes.getKeypair_return kid w v key a b run).1

private theorem index (action : IndexM α) : SameView dropped (liftIndex action) := by
  intro initial
  apply hoare_liftIndex
  intro w d table hi device
  simpa only [dropped,device,Option.map_some] using hi

macro "rejection_drop_step " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head getPeer; exact (read_peer _).wp (· = $initial))
  | (rx_retention_head getKeypair; exact (read_key _).wp (· = $initial))
  | (rx_retention_head setPeer; apply (edit _ ?_).wp (· = $initial); intro d; rfl)
  | (rx_retention_head setKeypair; apply (edit _ ?_).wp (· = $initial); intro d; rfl)
  | (rx_retention_head modifyDev; apply (edit _ ?_).wp (· = $initial); intro d; rfl)
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (rx_retention_head branch; unfold branch; exact hoare_liftAmbient _ _)
  | (rx_retention_head branchExpired; exact ((branchExpired_sameWGWorld _ _ _ _).factor dropped).wp (· = $initial))
  | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM; exact (index _).wp (· = $initial))
  | (rx_retention_head ForIn.forIn; apply TransmitSecurity.Nonce.Frames.loop; intro x b)
  | rx_retention_step)

theorem key_put_dropped (kid : KeypairId) : SameView dropped (keypairPut (some kid) false) := by
  intro initial
  change Preserves (fun w => dropped w = initial) _
  unfold keypairPut refcountDecAndTest
  simp (config := {zeta := false}) only [branch,branchCmp,unsupported,indexRemove_eq]
  repeat' rejection_drop_step initial

theorem rejection_prefix_dropped (pid : PeerId) (packets : List Packet) (kid : KeypairId) :
    SameView dropped (do invalidate kid; release kid packets; restore pid packets) := by
  intro initial
  change Preserves (fun w => dropped w = initial) _
  unfold invalidate release restore
  repeat' first
    | (rx_retention_head keypairPut; exact (key_put_dropped _).wp (· = initial))
    | rejection_drop_step initial

end Leanux.Proofs.WG.HandshakeSecurity.NonceRejection
