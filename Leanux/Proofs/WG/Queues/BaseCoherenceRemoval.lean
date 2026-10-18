import Leanux.Proofs.WG.Queues.BaseCoherence
import Leanux.Proofs.WG.Queues.HolderWorkFrames
import Leanux.Proofs.WG.Origins.ConfiguredHandshake
import Leanux.Proofs.WG.Peers.ConfiguredTimers
import Leanux.Proofs.WG.Lifetimes.PeerRemoval

/-! Actual removal preserves base-list/table coherence. The post-detachment
work and final payments retain these fields even when a peer is deleted.
All contracts are partial: stopped executions have no invented final state. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

private theorem combined_frame {α : Type} {action : WG.M α}
    (passive : ∀ initial, Preserves (DurableHolders.Frame initial) action)
    (configured : SameView ConfiguredIdentity.view action) : SameView view action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have fields := (hoare_iff_run_ambient _ _ _).mp (passive w)
    w a result v b (DurableHolders.Frame.refl w) run
  have table := (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherence.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.rows_of_configured)
    ((ProjectedAction.iff_run_ambient _ _ _).mp configured w a result v b run)
  have list : slots v = slots w := congrArg Prod.fst fields.passive
  exact Prod.ext list table

private theorem structural_store {α : Type} {action : WG.M α}
    (same : SameWGStore action) : SameView view action :=
  same.of_factor (fun s : WGStoreView => view {dev := s.dev}) view (fun _ => rfl)

private theorem structural_read (pid : PeerId) : SameView view (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  exact congrArg view (getPeer_normal pid w v p a b run).1

private theorem structural_update (f : Device → Device)
    (list : ∀ d, (f d).peerList = d.peerList)
    (table : ∀ d, (f d).peerHashtable = d.peerHashtable) :
    SameView view (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases run
  simp only [view,slots,rows,Option.map_map,Function.comp_def,list,table]

private theorem structural_index {α : Type} (action : IndexM α) :
    SameView view (liftIndex action) := by
  intro initial
  apply hoare_liftIndex
  intro w d table hi hd
  simpa only [view,slots,rows,hd,Option.map_some,Option.getD_some] using hi

private theorem structural_write (pid : PeerId) (p : Peer) : SameView view (setPeer pid p) :=
  structural_update _ (fun _ => rfl) (fun _ => rfl)

macro "base_structure_step " initial:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head getPeer; exact (structural_read _).wp (fun s => s = $initial))
  | (rx_retention_head getDev; exact (structural_store getDev_sameWGStore).wp (fun s => s = $initial))
  | (rx_retention_head setPeer; exact (structural_write _ _).wp (fun s => s = $initial))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (rx_retention_head modifyDev
     apply (structural_update _ ?_ ?_).wp (fun s => s = $initial)
     all_goals intro d; rfl)
  | (rx_retention_head modify; apply hoare_modify; intro w hi; exact hi)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM; exact (structural_index _).wp (fun s => s = $initial))
  | (rx_retention_head ForIn.forIn; apply list_view_spec view (fun s => s = $initial); intro x acc; change Preserves (fun w => view w = $initial) _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi hr
     cases hr)
  | rx_retention_step)

/-- Final release can delete a peer while leaving both structural fields intact. -/
theorem peerPut_view (pid : Option PeerId) : SameView view (peerPut pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold peerPut refcountDecAndTest retirePeerUnits
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,
    invariant,unsupported,modifyAmbient]
  repeat' base_structure_step initial

theorem keypairsClear_view (pid : PeerId) : SameView view (keypairsClear pid) :=
  combined_frame (HolderWorkFrames.keypairsClear_frame pid) (ConfiguredMaintenance.keypairsClear_view pid)

theorem handshakeClear_view (pid : PeerId) : SameView view (handshakeClear pid) :=
  combined_frame (HolderWorkFrames.handshakeClear_frame pid) (ConfiguredMaintenance.handshakeClear_view pid)

theorem queuedClear_view (pid : PeerId) : SameView view (queuedExpiredZeroKeyMaterial pid) := by
  unfold queuedExpiredZeroKeyMaterial
  exact (handshakeClear_view pid).bind (fun _ => (keypairsClear_view pid).bind (fun _ => peerPut_view (some pid)))

theorem sendHandshakeInitiation_view (pid : PeerId) : SameView view (sendHandshakeInitiation pid) :=
  combined_frame (HolderWorkFrames.sendHandshakeInitiation_frame pid) (ConfiguredHandshake.sendHandshakeInitiation_view pid)

theorem handshakeSendWorker_view (pid : PeerId) : SameView view (handshakeSendWorker pid) := by
  unfold handshakeSendWorker
  exact (sendHandshakeInitiation_view pid).bind (fun _ => peerPut_view (some pid))

theorem delTimer_view (pid : PeerId) (timer : PeerTimer) : SameView view (delTimer pid timer) :=
  combined_frame ((pinned_const _private.Leanux.Proofs.WG.Queues.HolderWorkFrames.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderWorkFrames.del_preserves) pid timer)
    (ConfiguredIdentity.delTimer_view pid timer)

theorem flushedSend_view (pid : PeerId) : SameView view (runFlushedSendWork pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold runFlushedSendWork
  simp (config := {zeta := false}) only [invariant,hidden]
  repeat' first
    | (rx_retention_head handshakeSendWorker; exact (handshakeSendWorker_view _).wp (fun s => s = initial))
    | base_structure_step initial

theorem flushedClear_view (pid : PeerId) : SameView view (runFlushedClearWork pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold runFlushedClearWork
  simp (config := {zeta := false}) only [hidden]
  repeat' first
    | (rx_retention_head queuedExpiredZeroKeyMaterial; exact (queuedClear_view _).wp (fun s => s = initial))
    | base_structure_step initial

/-- The finite source drain preserves structure in recorded dispatch order,
including either early exit and the placeholder queue-selection branches. -/
theorem drain_view (upTo : Option PeerId) : SameView view (drainHandshakeSendWq upTo) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',
    peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (rx_retention_head runFlushedSendWork; exact (flushedSend_view _).wp (fun s => s = initial))
    | (rx_retention_head runFlushedClearWork; exact (flushedClear_view _).wp (fun s => s = initial))
    | base_structure_step initial

theorem timersStop_view (pid : PeerId) : SameView view (timersStop pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold timersStop
  repeat' first
    | (rx_retention_head delTimer; exact (delTimer_view _ _).wp (fun s => s = initial))
    | (rx_retention_head drainHandshakeSendWq; exact (drain_view _).wp (fun s => s = initial))
    | base_structure_step initial

theorem afterDead_view (pid : PeerId) : SameView view (peerRemoveAfterDead pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (rx_retention_head keypairsClear; exact (keypairsClear_view _).wp (fun s => s = initial))
    | (rx_retention_head timersStop; exact (timersStop_view _).wp (fun s => s = initial))
    | (rx_retention_head drainHandshakeSendWq; exact (drain_view _).wp (fun s => s = initial))
    | (rx_retention_head peerPut; exact (peerPut_view _).wp (fun s => s = initial))
    | base_structure_step initial

theorem free_view : SameView view WG.free := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have base := (ProjectedAction.iff_run_ambient _ _ _).mp BaseRemoval.allowedipsFree_view w a result v b run
  have configured := (ProjectedAction.iff_run_ambient _ _ _).mp ConfiguredIdentity.allowedipsFree_view w a result v b run
  exact Prod.ext (congrArg (fun s => s.2.getD []) base)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherence.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.rows_of_configured) configured)

private theorem preserves_of_view {α : Type} {action : WG.M α}
    (same : SameView view action) : Preserves Inv action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact transport hi ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)

private theorem makeDead_spec (pid : PeerId) : Preserves Inv (peerMakeDead pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  exact makeDead_preserves pid hi a b run

/-- Single removal needs only structural coherence, with no resident or
positive-reference premise. Its actual post-detachment drains and final put run. -/
theorem peerRemove_preserves (peer : Option PeerId) : Preserves Inv (peerRemove peer) := by
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerMakeDead; exact makeDead_spec _)
    | (rx_retention_head peerRemoveAfterDead; exact preserves_of_view (afterDead_view _))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

/-- The actual bulk source first detaches each saved-list entry, then performs
each post-detachment removal, retaining its branch records and work drains. -/
theorem peerRemoveAll_preserves : Preserves Inv peerRemoveAll := by
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.free; exact preserves_of_view free_view)
    | (rx_retention_head getDev; exact preserves_of_view (structural_store getDev_sameWGStore))
    | (rx_retention_head peerMakeDead; exact makeDead_spec _)
    | (rx_retention_head peerRemoveAfterDead; exact preserves_of_view (afterDead_view _))
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ForIn.forIn; apply list_view_spec id Inv; intro x acc; change Preserves Inv _)
    | rx_retention_step

theorem peerRemove_observed (peer : Option PeerId) (hi : Inv w) (a b : Ambient) (history)
    (run : (runStatePrefix (peerRemovePrefix peer) w a history).1 = .ok (((),v),b)) : Inv v :=
  (hoare_iff_run_ambient _ _ _).mp (peerRemove_preserves peer) w a () v b hi
    ((peerRemovePrefix_erases peer w a history).symm.trans run)

theorem peerRemoveAll_observed (hi : Inv w) (a b : Ambient) (history)
    (run : (runStatePrefix peerRemoveAllPrefix w a history).1 = .ok (((),v),b)) : Inv v :=
  (hoare_iff_run_ambient _ _ _).mp peerRemoveAll_preserves w a () v b hi
    ((peerRemoveAllPrefix_erases w a history).symm.trans run)

end Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence
