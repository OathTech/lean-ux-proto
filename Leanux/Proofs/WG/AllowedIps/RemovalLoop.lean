import Leanux.Proofs.WG.AllowedIps.RemovalLists

/-! The original for-in body runs over a saved list. Owned entry membership
and distinct saved IDs, rather than a changing live list, justify every step. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

structure RemovedIds (d out : WG.Device) (t4 t6 : Tree) (ids : List Nat) : Prop where
  forest : ForestRep out (t4.eraseIds ids) (t6.eraseIds ids)
  nextNode : out.nextNode = d.nextNode
  seq : out.peerAllowedips.seq = d.peerAllowedips.seq
  peers : ∀ pid : Nat, out.peers[pid]? = (d.peers[pid]?).map (unlistIds ids)
  outside : ∀ q, q ∉ t4.nodeIds ++ t6.nodeIds → out.nodes[q]? = d.nodes[q]?
  retired : ∀ q ∈ t4.nodeIds ++ t6.nodeIds,
    q ∉ (t4.eraseIds ids).nodeIds ++ (t6.eraseIds ids).nodeIds → out.nodes[q]? = none
  frame : out = {d with nodes := out.nodes, peers := out.peers, peerAllowedips := out.peerAllowedips}
  below : NodesBelow d → NodesBelow out

theorem RemovedIds.nil (hf : ForestRep d t4 t6) : RemovedIds d d t4 t6 [] := by
  refine ⟨hf, rfl, rfl, ?_, fun _ _ => rfl, ?_, rfl, fun h => h⟩
  · intro pid
    change d.peers[pid]? = (d.peers[pid]?).map (unlistIds [])
    cases d.peers[pid]? <;> simp
  · intro q hq hnot; exact False.elim (hnot hq)

theorem RemovedIds.cons {id : Nat} (a : RemovedForest d mid t4 t6 id)
    (b : RemovedIds mid out (t4.eraseId id) (t6.eraseId id) ids) :
    RemovedIds d out t4 t6 (id :: ids) := by
  have hsub : ∀ q, q ∈ (t4.eraseId id).nodeIds ++ (t6.eraseId id).nodeIds →
      q ∈ t4.nodeIds ++ t6.nodeIds := fun q h =>
    List.mem_append.mp h |>.elim
      (fun h => List.mem_append_left _ ((Tree.eraseId_nodeIds t4 id).subset h))
      (fun h => List.mem_append_right _ ((Tree.eraseId_nodeIds t6 id).subset h))
  refine ⟨b.forest, b.nextNode.trans a.metadata.1, b.seq.trans a.metadata.2.1, ?_, ?_, ?_, ?_,
    fun h => b.below (a.below h)⟩
  · intro pid
    rw [b.peers, a.metadata.2.2, Option.map_map]
    congr 1
    funext p
    exact (unlistIds_cons id ids p).symm
  · intro q hq
    exact (b.outside q (fun h => hq (hsub q h))).trans (a.outside q hq)
  · intro q hq hgone
    by_cases hm : q ∈ (t4.eraseId id).nodeIds ++ (t6.eraseId id).nodeIds
    · exact b.retired q hm hgone
    · exact (b.outside q hm).trans (a.retired q hq hm)
  · calc
      out = {mid with nodes := out.nodes, peers := out.peers, peerAllowedips := out.peerAllowedips} := b.frame
      _ = {d with nodes := out.nodes, peers := out.peers, peerAllowedips := out.peerAllowedips} := by
        rw [a.frame]

theorem remove_saved_total (ids : List Nat) (w : WGWorld) (ambient : Ambient) (d : WG.Device)
    (hd : w.dev = some d) (t4 t6 : Tree) (hf : ForestRep d t4 t6)
    (hn4 : t4.nodeIds.Nodup) (hn6 : t6.nodeIds.Nodup)
    (hc4 : t4.Compressed) (hc6 : t6.Compressed)
    (hn : ids.Nodup) (ho : OwnedIds ids t4 t6) :
    ∃ out w' ambient', ((forIn ids () (fun id _ => removeStep id) : WG.M Unit).run w).run ambient = .ok (((), w'), ambient') ∧
      w' = {w with dev := some out} ∧ RemovedIds d out t4 t6 ids := by
  induction ids generalizing w ambient d t4 t6 with
  | nil =>
    exact ⟨d, w, ambient, rfl, by rw [← hd], RemovedIds.nil hf⟩
  | cons id ids ih =>
    obtain ⟨mid, wm, am, he, hk, hs⟩ := remove_forest_total w ambient d hd t4 t6 id hf hn4 hn6 hc4 hc6
      (ho.member (List.mem_cons_self))
    obtain ⟨out, wf, af, he', hk', hs'⟩ := ih wm am mid (by rw [hk]) (t4.eraseId id) (t6.eraseId id)
      hs.forest ((Tree.eraseId_nodeIds t4 id).nodup hn4) ((Tree.eraseId_nodeIds t6 id).nodup hn6)
      (Tree.eraseId_compressed t4 id) (Tree.eraseId_compressed t6 id)
      (List.nodup_cons.mp hn).2 (ho.tail hn)
    refine ⟨out, wf, af, ?_, ?_, RemovedIds.cons hs hs'⟩
    · simp only [List.forIn_cons, StateT.run_bind, he]
      exact he'
    · rw [hk', hk]

theorem RemovedIds.coherent (h : RemovedIds d out t4 t6 ids) (hc : ResidentLists d t4 t6) :
    ResidentLists out (t4.eraseIds ids) (t6.eraseIds ids) :=
  residentLists_filtered hc ids h.peers

end Leanux.Proofs.WG.AllowedIps
