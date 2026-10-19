import Leanux.Proofs.WG.RetirementSecurity.AllRxDisposal

/-! Peer and queue bookkeeping retain the complete key store. These native
frames carry rejection invalidation through the actual requeue suffix. -/
namespace Leanux.Proofs.WG.RetirementSecurity.Invalidation
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Std.Do

theorem update (f : Device → Device) (keys : ∀ d, (f d).keypairs = d.keypairs) :
    SameView keyAt (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b hr
  cases hr
  funext id
  simp [keyAt, Option.bind_map, Function.comp_def, keys]

theorem peer_read (pid : PeerId) : SameView keyAt (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b hr
  exact congrArg keyAt (Peers.getPeer_current pid w v p a b hr).1

theorem key_read (kid : KeypairId) : SameView keyAt (getKeypair kid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a k v b hr
  exact congrArg keyAt (Keypairs.getKeypair_current kid w v a b k hr).1

theorem peer_write (pid : PeerId) (p : Peer) : SameView keyAt (setPeer pid p) :=
  update _ (fun _ => rfl)

theorem index {α : Type} (a : IndexM α) : SameView keyAt (liftIndex a) := by
  intro initial
  apply hoare_liftIndex
  intro w d table hi hd
  rw [← hi]
  funext id
  simp [keyAt,hd]

macro "retirement_validity_frame_step " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head getPeer; exact (peer_read _).wp (fun s => s = $initial))
  | (rx_retention_head getKeypair; exact (key_read _).wp (fun s => s = $initial))
  | (rx_retention_head setPeer; exact (peer_write _ _).wp (fun s => s = $initial))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (rx_retention_head modifyDev
     apply (update _ ?_).wp (fun s => s = $initial)
     intro d; rfl)
  | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM; exact (index _).wp (fun s => s = $initial))
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi hr
     cases hr)
  | rx_retention_step)

theorem peerGet (pid : PeerId) : SameView keyAt (WG.peerGet pid) := by
  intro initial
  change Preserves (fun w => keyAt w = initial) _
  unfold WG.peerGet refcountInc
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,unsupported]
  repeat' retirement_validity_frame_step initial

theorem peerPut (pid : Option PeerId) : SameView keyAt (WG.peerPut pid) := by
  intro initial
  change Preserves (fun w => keyAt w = initial) _
  unfold WG.peerPut refcountDecAndTest retirePeerUnits
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,
    invariant,unsupported,modifyAmbient]
  repeat' retirement_validity_frame_step initial

theorem queuedHandshake (pid : PeerId) (retry : Bool) :
    SameView keyAt (sendQueuedHandshakeInitiation pid retry) := by
  intro initial
  change Preserves (fun w => keyAt w = initial) _
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' first
    | (rx_retention_head WG.peerGet; exact (peerGet _).wp (fun s => s = initial))
    | (rx_retention_head WG.peerPut; exact (peerPut _).wp (fun s => s = initial))
    | (rx_retention_head branchExpired; exact ((branchExpired_sameWGWorld _ _ _ _).factor keyAt).wp (fun s => s = initial))
    | retirement_validity_frame_step initial

end Leanux.Proofs.WG.RetirementSecurity.Invalidation
