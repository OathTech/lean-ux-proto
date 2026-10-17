import Leanux.Proofs.WG.Queues.RxClearQueue

/-! The durable send/clear queue lists are separate from peer reference counts.
Release may erase a peer but does not silently erase a queued work occurrence. -/
namespace Leanux.Proofs.WG.Queues.WorkQueueFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

def view (w : WGWorld) := w.dev.map fun d => (d.ifindex,d.sendWorkQueue,d.clearWorkQueue)

theorem store {α : Type} {a : WG.M α} (ha : SameWGStore a) : SameView view a :=
  ha.of_factor (fun s : WGStoreView => s.dev.map fun d => (d.ifindex,d.sendWorkQueue,d.clearWorkQueue))
    view (fun _ => rfl)

theorem update (f : Device → Device) (epoch : ∀ d, (f d).ifindex = d.ifindex)
    (send : ∀ d, (f d).sendWorkQueue = d.sendWorkQueue)
    (clear : ∀ d, (f d).clearWorkQueue = d.clearWorkQueue) : SameView view (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b hr
  cases hr
  simp [view,Option.map_map,Function.comp_def,epoch,send,clear]

private theorem peer_read (pid : PeerId) : SameView view (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b hr
  exact congrArg view (getPeer_normal pid w v p a b hr).1

private theorem key_read (kid : KeypairId) : SameView view (getKeypair kid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a k v b hr
  exact congrArg view (KeyTimes.getKeypair_return kid w v k a b hr).1

private theorem peer_write (pid : PeerId) (p : Peer) : SameView view (setPeer pid p) :=
  update _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

private theorem key_write (kid : KeypairId) (k : Keypair) : SameView view (setKeypair kid k) :=
  update _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

private theorem index {α : Type} (a : IndexM α) : SameView view (liftIndex a) := by
  intro initial
  apply hoare_liftIndex
  intro w d table hi hd
  simpa [view,hd] using hi

macro "work_queue_step " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head getPeer; exact (peer_read _).wp (fun s => s = $initial))
  | (rx_retention_head getKeypair; exact (key_read _).wp (fun s => s = $initial))
  | (rx_retention_head setPeer; exact (peer_write _ _).wp (fun s => s = $initial))
  | (rx_retention_head setKeypair; exact (key_write _ _).wp (fun s => s = $initial))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (rx_retention_head modifyDev
     apply (update _ ?_ ?_ ?_).wp (fun s => s = $initial)
     all_goals intro d; rfl)
  | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM; exact (index _).wp (fun s => s = $initial))
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi hr
     cases hr)
  | rx_retention_step)

theorem peerGet_frame (pid : PeerId) : SameView view (peerGet pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold peerGet refcountInc
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,unsupported]
  repeat' work_queue_step initial

theorem peerPut_frame (pid : Option PeerId) : SameView view (peerPut pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold peerPut refcountDecAndTest retirePeerUnits
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,
    invariant,unsupported,modifyAmbient]
  repeat' work_queue_step initial

theorem keypairPut_frame (kid : Option KeypairId) (now : Bool) :
    SameView view (keypairPut kid now) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold keypairPut refcountDecAndTest
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' work_queue_step initial

theorem handshakeClear_frame (pid : PeerId) : SameView view (handshakeClear pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold handshakeClear handshakeZero
  repeat' work_queue_step initial

theorem keypairsClear_frame (pid : PeerId) : SameView view (keypairsClear pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' first
    | (rx_retention_head keypairPut; exact (keypairPut_frame _ _).wp (fun s => s = initial))
    | work_queue_step initial

theorem queuedClear_frame (pid : PeerId) : SameView view (queuedExpiredZeroKeyMaterial pid) := by
  unfold queuedExpiredZeroKeyMaterial
  exact (handshakeClear_frame pid).bind (fun _ =>
    (keypairsClear_frame pid).bind (fun _ => peerPut_frame (some pid)))

theorem clear_factor (w : WGWorld) :
    RxCredits.ClearWork.queueView w = (view w).map (fun q => (q.1,q.2.2)) := by
  simp only [RxCredits.ClearWork.queueView,view,Option.map_map,Function.comp_def]

theorem queuedClear_clear (pid : PeerId) :
    SameView RxCredits.ClearWork.queueView (queuedExpiredZeroKeyMaterial pid) :=
  (queuedClear_frame pid).of_factor (fun q => q.map (fun q => (q.1,q.2.2)))
    RxCredits.ClearWork.queueView (fun w => clear_factor w)

end Leanux.Proofs.WG.Queues.WorkQueueFrames
