import Leanux.Proofs.WG.Queues.RxStackFrames
import Leanux.Proofs.WG.Queues.RxPollProjection
import Init.Data.List.Perm

/-! Per-poll callback occurrence provenance and concrete entry-queue order.
Callbacks may be selected out of chronological order, and their entry events
include a failing callback. No allocation-identity or completed-delivery claim
is made by these local occurrence statements. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem selectedEntries_perm (entries : List GroEntry) :
    (selectedEntries entries).Perm entries := by
  simpa only [selectedEntries, normalEntries, heldEntries] using
    List.filter_append_perm (fun e => groTakenAtOnce e.bytes) entries

theorem callback_tag_properties (h : List GroEvent) (hs : SelectedGroSafe h) (ht : TagSafe h) :
    ((enteredEntries h).map GroEntry.occurrence).Nodup ∧
      ∀ e ∈ enteredEntries h,
        e ∈ bufferedEntries h ∧ (e.occurrence, e.skb) ∈ removedTags h := by
  obtain ⟨remaining, hs⟩ := hs
  change selectedEntries (bufferedEntries h) = enteredEntries h ++ remaining at hs
  have hp := selectedEntries_perm (bufferedEntries h)
  have he : (enteredEntries h).Sublist (selectedEntries (bufferedEntries h)) := by
    rw [hs]
    exact List.sublist_append_left _ _
  have hb := ht.properties
  refine ⟨(he.map GroEntry.occurrence).nodup ((hp.map GroEntry.occurrence).symm.nodup hb.2.2), ?_⟩
  intro e hen
  have heb : e ∈ bufferedEntries h := hp.subset (he.subset hen)
  exact ⟨heb, hb.1.subset (List.mem_map.mpr ⟨e, heb, rfl⟩)⟩

theorem rxPollGro_callback_provenance (pid : PeerId) (budget : Nat) (w : World) :
    let h := (runPrefix (rxPollGro pid budget) w []).2
    ((enteredEntries h).map GroEntry.occurrence).Nodup ∧
      ∀ e ∈ enteredEntries h,
        e ∈ bufferedEntries h ∧ (e.occurrence, e.skb) ∈ removedTags h :=
  callback_tag_properties _ (rxPollGro_selected_prefix pid budget w) (rxPollGro_tags_safe pid budget w)

/-- The concrete original stack callback discharges the callback frame of
the removal-prefix theorem. The initial resident identifies the entry queue;
arbitrary packet IDs and all later Stops remain covered. -/
theorem rxPollGro_entry_prefix (pid : PeerId) (budget : Nat) (w : World) (cell : RxQueueCell)
    (hc : rxQueues w.wg pid = some cell) :
    RemovalPrefix cell.queue.all
      ((removedTags (runPrefix (rxPollGro pid budget) w []).2).map Prod.snd) := by
  have hp := rxPollRemovals_prefix pid budget (fun bytes => bytes.forM Leanux.Env.deliverInner)
    w cell stackForM_rxQueues hc
  simpa only [rxPollGro_removals_agree] using hp

theorem rxPollGro_buffered_sublist (pid : PeerId) (budget : Nat) (w : World) (cell : RxQueueCell)
    (hc : rxQueues w.wg pid = some cell) :
    ((bufferedEntries (runPrefix (rxPollGro pid budget) w []).2).map GroEntry.skb).Sublist
      cell.queue.all := by
  have hb := (rxPollGro_tags_properties pid budget w).1.map Prod.snd
  obtain ⟨tail, he⟩ := rxPollGro_entry_prefix pid budget w cell hc
  rw [he]
  have hs := hb.trans (List.sublist_append_left _ tail)
  simpa only [bufferedTags, List.map_map, Function.comp_def] using hs

end Leanux.Proofs.WG.Queues
