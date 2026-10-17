import Leanux.Proofs.WG.Config.AllowedListFrames
import Leanux.Proofs.WG.Config.AllowedLists

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

def eraseListedPeer (id : NodeId) (p : Peer) : Peer :=
  { p with allowedipsList := listRemove p.allowedipsList id }

def listDeleteView (id : NodeId) (initial current : Device) (seen : List PeerId) : Prop :=
  ∀ q, current.peers[q]? =
    if q ∈ seen then initial.peers[q]?.map (eraseListedPeer id) else initial.peers[q]?

theorem deleteListedNode_view (id : NodeId) (initial current : Device) (seen : List PeerId)
    (pid : PeerId) (p : Peer) (resident : initial.peers[pid]? = some p)
    (view : listDeleteView id initial current seen) :
    listDeleteView id initial (deleteListedNode id current (pid, p)) (pid :: seen) := by
  intro q
  cases contains : p.allowedipsList.contains id with
  | false =>
      have absent : id ∉ p.allowedipsList := by simpa using contains
      have unchanged : eraseListedPeer id p = p := by
        simp [eraseListedPeer, listRemove, List.filter_bne_eq_self_of_not_mem absent]
      by_cases same : q = pid
      · subst q
        simp [deleteListedNode, absent, view pid, resident, unchanged]
      · simp [deleteListedNode, absent, view q, same]
  | true =>
      have present : id ∈ p.allowedipsList := by simpa using contains
      by_cases same : q = pid
      · subst q
        simp [deleteListedNode, present, resident, eraseListedPeer]
      · simp [deleteListedNode, present, Std.TreeMap.getElem?_insert, Ne.symm same, same, view q]

theorem deleteListedNodes_view (id : NodeId) (initial current : Device) (seen : List PeerId)
    (entries : List (PeerId × Peer))
    (snapshot : ∀ entry ∈ entries, initial.peers[entry.1]? = some entry.2)
    (view : listDeleteView id initial current seen) :
    listDeleteView id initial (deleteListedNodes id current entries) (entries.map Prod.fst ++ seen) := by
  induction entries generalizing current seen with
  | nil => simpa [deleteListedNodes] using view
  | cons entry rest ih =>
      have step := deleteListedNode_view id initial current seen entry.1 entry.2
        (snapshot entry (by simp)) view
      have tail := ih (deleteListedNode id current entry) (entry.1 :: seen)
        (fun item member => snapshot item (by simp [member])) step
      intro q
      have hq := tail q
      simp only [deleteListedNodes, List.foldl_cons, List.map_cons, List.cons_append,
        List.mem_append, List.mem_cons] at hq ⊢
      simpa only [or_assoc, or_left_comm, or_comm] using hq

theorem deleteListedNodes_lookup (id : NodeId) (d : Device) (q : PeerId) :
    (deleteListedNodes id d d.peers.toList).peers[q]? = d.peers[q]?.map (eraseListedPeer id) := by
  have view := deleteListedNodes_view id d d [] d.peers.toList
    (fun entry member => Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member)
    (by intro q; simp)
  have hq := view q
  simp only [List.append_nil] at hq
  cases found : d.peers[q]? with
  | none => simpa [found] using hq
  | some p =>
      have member : (q, p) ∈ d.peers.toList :=
        Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr found
      have seen : q ∈ d.peers.toList.map Prod.fst := List.mem_map.mpr ⟨(q, p), member, rfl⟩
      simpa only [ite_eq_left seen, found, Option.map_some] using hq

theorem listDel_peer_lists (id : NodeId) (d : Device) :
    Returns (listDel id) (fun w => w.dev = some d)
      (fun _ w => ∃ final, w.dev = some final ∧
        ∀ q : PeerId, final.peers[q]? = d.peers[q]?.map (eraseListedPeer id)) := by
  intro w ambient h
  obtain ⟨result, final, after, run, post⟩ := listDel_returns id d w ambient h
  exact ⟨result, final, after, run, deleteListedNodes id d d.peers.toList, post,
    deleteListedNodes_lookup id d⟩

end Leanux.Proofs.WG.Config
