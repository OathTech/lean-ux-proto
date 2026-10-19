import Leanux.Proofs.WG.TransmitSecurity.StagedSelectionFrames

/-! Exact staged queue frames through native key and peer reference operations. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Exact
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem read_peer (pid : PeerId) : SameView stagedAt (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  exact congrArg stagedAt (getPeer_normal pid w v p a b run).1

theorem read_key (kid : KeypairId) : SameView stagedAt (getKeypair kid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a key v b run
  exact congrArg stagedAt (KeyTimes.getKeypair_return kid w v key a b run).1

theorem modify_device (f : Device → Device) (peers : ∀ d, (f d).peers = d.peers) :
    SameView stagedAt (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  cases run
  funext pid
  simp only [stagedAt,Option.bind_map,Function.comp_def,peers]

theorem index (action : IndexM α) : SameView stagedAt (liftIndex action) := by
  intro initial
  apply hoare_liftIndex
  intro w d table before device
  rw [← before]
  funext pid
  simp only [stagedAt,device,Option.bind_some]

theorem modify_preserves (f : Device → Device) (initial)
    (peers : ∀ d, (f d).peers = d.peers) :
    Preserves (fun w => stagedAt w = initial) (modifyDev f) :=
  (modify_device f peers).wp (· = initial)

theorem key_put (kid : Option KeypairId) (now : Bool) : SameView stagedAt (keypairPut kid now) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold keypairPut refcountDecAndTest
  simp (config := {zeta := false}) only [branch,branchCmp,unsupported,invariant]
  repeat' first
    | (rx_retention_head getKeypair; exact (read_key _).wp (· = initial))
    | (rx_retention_head setKeypair; exact (Origins.set_key_staged _ _).wp (· = initial))
    | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
    | (rx_retention_head modifyDev; apply modify_preserves; intro d; rfl)
    | (allocation_release_lift_from IndexM; exact (index _).wp (· = initial))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem peer_get (pid : PeerId) : SameView stagedAt (peerGet pid) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold peerGet
  apply preserves_bind
  · unfold requireNotPending
    exact preserves_pure _
  · intro _
    apply hoare_bind _ _ (Staged.read_saved (fun s => s = initial) pid)
    intro peer
    have counted : Preserves
        (fun w => stagedAt w = initial ∧ stagedAt w pid = some (peer.internalId,peer.staged))
        (refcountInc peer.refcount : WG.M Unit) := by
      unfold refcountInc
      simp only [branch,branchCmp,unsupported]
      repeat' first
        | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
        | rx_retention_step
    apply hoare_bind _ _ counted
    intro _
    exact Staged.write_saved (fun s => s = initial) pid {peer with refcount := peer.refcount+1}

end Leanux.Proofs.WG.TransmitSecurity.Staged.Exact
