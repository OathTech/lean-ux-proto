import Leanux.Proofs.WG.TransmitSecurity.StagedOriginNativeFrames

/-! Selection clears one queue and borrows its current key. The key borrow
preserves every staged occurrence and peer stamp exactly. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem Inv.clear (before : Inv h w) (pid : PeerId) (p : Peer) :
    Inv h {w with dev := w.dev.map fun d => {d with peers := d.peers.insert pid {p with staged := []}}} := by
  cases device : w.dev with
  | none =>
    intro generation epoch
    simp [Packets.epoch] at epoch
  | some d =>
    simp only [Option.map_some]
    have slot : stagedAt {w with dev := some {d with peers := d.peers.insert pid {p with staged := []}}} pid =
        some (p.internalId,[]) := by simp [stagedAt]
    simpa only [List.append_nil] using before.changed (generation := d.ifindex) []
      (by simp [Packets.epoch,device]) (by simp [Packets.epoch]) slot
      (fun q different => by simp [stagedAt,device,Std.TreeMap.getElem?_insert,Ne.symm different]) Batch.nil

theorem set_key_staged (kid : KeypairId) (key : Keypair) : SameView stagedAt (setKeypair kid key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b run
  cases run
  funext pid
  simp only [stagedAt,Option.bind_map,Function.comp_def]

theorem key_get_staged (kid : Option KeypairId) : SameView stagedAt (keypairGet kid) := by
  intro initial
  change Preserves (fun w => stagedAt w = initial) _
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta := false}) only [branch,branchCmp,unsupported,invariant]
  repeat' first
    | (rx_retention_head getKeypair
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a key v b before run
       exact (KeyTimes.getKeypair_return _ w v key a b run).1 ▸ before)
    | (rx_retention_head setKeypair; exact (set_key_staged _ _).wp (· = initial))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
