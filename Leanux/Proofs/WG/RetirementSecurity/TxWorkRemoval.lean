import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionRemoval
import Leanux.Proofs.WG.RetirementSecurity.TxCoveragePeerRemoval

/-! Native peer removal retains converse TX service. Its actual fail-closed
crypt-work guard is preserved; cleanup does not count identity retirement as
a native packet disposal. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem aip_work (action : AipM α) : SameView queued (liftAip action) := by
  intro initial
  apply hoare_liftAip action
  intro w d table before device
  simpa only [queued,device,Option.map_some,Option.getD_some] using before

theorem aip_list_delete_work (id : NodeId) : SameView queued (listDel id) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold listDel
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec _root_.id (fun w=>queued w=initial)
       intro item state
       change Preserves (fun w=>queued w=initial) _)
    | tx_work_step initial

theorem aip_remove_work (pid : PeerId) : SameView queued (removeByPeer pid) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold removeByPeer AipNode.bitAt
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_lift_from AipM; exact (aip_work _).wp (·=initial))
    | (rx_retention_head listDel; exact (aip_list_delete_work _).wp (·=initial))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w=>queued w=initial)
       intro item state
       change Preserves (fun w=>queued w=initial) _)
    | key_work_step initial

theorem aip_free_work : SameView queued WG.free := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have kept := (hoare_iff_run_ambient _ _ _).mp (AllowedIps.free_storeView (wgStoreView w))
    w a result v b rfl run
  have fields := congrArg (fun s : WGStoreView × (PeerId→Option Peer)=>queued {dev:=s.1.dev}) kept
  simpa only [AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,AllowedIps.resetAllowedips,
    queued,wgStoreView,Option.map_map,Function.comp_def] using fields

theorem serving_aip_remove (pid : PeerId) : Preserves (Serving locals crypt tx) (removeByPeer pid) :=
  serving_join (passive_contents (OccurrenceAllowedIps.remove_wire pid)
    (OccurrenceAllowedIps.remove_contents pid) (aip_remove_work pid)) (TxCovered.Removal.allowedips pid)

theorem serving_aip_free : Preserves (Serving locals crypt tx) WG.free :=
  serving_join (passive_contents OccurrenceAllowedIps.free_wire OccurrenceAllowedIps.free_contents aip_free_work)
    TxCovered.Removal.free_allowedips

theorem serving_clear (pid : PeerId) : Preserves (Serving locals crypt tx) (keypairsClear pid) :=
  serving_join (passive (OccurrenceKeys.clear_wire pid) (OccurrenceKeys.clear_queues pid) (clear_work pid))
    (TxCovered.join
      (RxPollOccurrences.join (keypairsClearPrefix_erases pid) (keypairsClearPrefix_allocation pid)
        (occurrence_passive (OccurrenceKeys.clear_wire pid) (OccurrenceKeys.clear_queues pid)))
      (TxCoverageNative.clear pid))

macro "serving_removal_step" : tactic => `(tactic| first
  | (rx_retention_head runFlushedSendWork; exact serving_flushed_send _)
  | (rx_retention_head runFlushedClearWork; exact serving_flushed_clear _)
  | (rx_retention_head keypairsClear; exact serving_clear _)
  | (rx_retention_head delTimer; exact serving_del _ _)
  | (rx_retention_head peerPut; exact serving_peer_put _)
  | (rx_retention_head removeByPeer; exact serving_aip_remove _)
  | (rx_retention_head WG.free; exact serving_aip_free)
  | (rx_retention_head throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b before run
     cases run)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (Serving _ _ _)
     intro item state
     change Preserves (Serving _ _ _) _)
  | serving_metadata_step)

theorem serving_drain (upTo : Option PeerId) :
    Preserves (Serving locals crypt tx) (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only
    [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' serving_removal_step

theorem serving_timers_stop (pid : PeerId) : Preserves (Serving locals crypt tx) (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (rx_retention_head drainHandshakeSendWq; exact serving_drain _)
    | serving_removal_step

theorem serving_after_dead (pid : PeerId) : Preserves (Serving locals crypt tx) (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (rx_retention_head timersStop; exact serving_timers_stop _)
    | (rx_retention_head drainHandshakeSendWq; exact serving_drain _)
    | serving_removal_step

theorem serving_make_dead (pid : PeerId) : Preserves (Serving locals crypt tx) (peerMakeDead pid) := by
  unfold peerMakeDead
  simp (config := {zeta := false}) only [branch]
  repeat' serving_removal_step

theorem serving_remove (pid : Option PeerId) : Preserves (Serving locals crypt tx) (peerRemove pid) := by
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerMakeDead; exact serving_make_dead _)
    | (rx_retention_head peerRemoveAfterDead; exact serving_after_dead _)
    | serving_removal_step

theorem serving_remove_all : Preserves (Serving locals crypt tx) peerRemoveAll := by
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head peerMakeDead; exact serving_make_dead _)
    | (rx_retention_head peerRemoveAfterDead; exact serving_after_dead _)
    | serving_removal_step

theorem remove_actor (pid : Option PeerId) :
    Preserves (At (Covered locals crypt) crypt active) (liftWG (peerRemove pid)) :=
  At.native (fun _=>serving_remove pid) (TxSuspension.peer_remove pid)

theorem remove_all_actor : Preserves (At (Covered locals crypt) crypt active) (liftWG peerRemoveAll) :=
  At.native (fun _=>serving_remove_all) TxSuspension.peer_remove_all

end Leanux.Proofs.WG.RetirementSecurity.TxWork
