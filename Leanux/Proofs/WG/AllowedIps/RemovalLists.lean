import Leanux.Proofs.WG.AllowedIps.RemovalDispatch

/-! Resident list coherence is conditional on actual peer residency. Raw
owner labels without a resident peer remain permitted. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux
set_option pp.structureInstances false

def ResidentLists (d : WG.Device) (t4 t6 : Tree) : Prop :=
  ∀ pid p, d.peers[pid]? = some p → p.allowedipsList.Nodup ∧
    ∀ id, id ∈ p.allowedipsList ↔
      ∃ e ∈ t4.entries ++ t6.entries, e.id = id ∧ e.peer = pid

def Tree.eraseIds (t : Tree) : List Nat → Tree
  | [] => t
  | id :: ids => (t.eraseId id).eraseIds ids

def unlistIds (ids : List Nat) (p : WG.Peer) : WG.Peer :=
  {p with allowedipsList := p.allowedipsList.filter (fun id => !ids.contains id)}

@[simp] theorem unlistIds_nil (p : WG.Peer) : unlistIds [] p = p := by
  simp [unlistIds, List.filter_eq_self.mpr (fun _ _ => rfl)]

theorem unlistIds_cons (id : Nat) (ids : List Nat) (p : WG.Peer) :
    unlistIds (id :: ids) p = unlistIds ids (unlist id p) := by
  simp [unlistIds, unlist, WG.listRemove, List.filter_filter, Bool.and_comm, bne, Bool.beq_eq_decide_eq]

theorem Tree.eraseIds_entries (t : Tree) (ids : List Nat) :
    (t.eraseIds ids).entries = t.entries.filter (fun e => !ids.contains e.id) := by
  induction ids generalizing t with
  | nil => simp [eraseIds, List.filter_eq_self.mpr (fun _ _ => rfl)]
  | cons id ids ih =>
    simp [eraseIds, ih, eraseId_entries, List.filter_filter, Bool.and_comm, bne, Bool.beq_eq_decide_eq]

theorem Tree.eraseIds_nodeIds (t : Tree) (ids : List Nat) :
    (t.eraseIds ids).nodeIds.Sublist t.nodeIds := by
  induction ids generalizing t with
  | nil => exact .refl _
  | cons id ids ih => exact (ih _).trans (eraseId_nodeIds t id)

theorem Tree.eraseIds_compressed (t : Tree) (ids : List Nat) (hc : t.Compressed) :
    (t.eraseIds ids).Compressed := by
  induction ids generalizing t with
  | nil => exact hc
  | cons id ids ih => exact ih _ (eraseId_compressed t id)

theorem Tree.eraseIds_valid (t : Tree) (ids : List Nat) (hv : t.Valid width) :
    (t.eraseIds ids).Valid width := by
  induction ids generalizing t with
  | nil => exact hv
  | cons id ids ih => exact ih _ (eraseId_valid hv id)

theorem Tree.entry_mem_nodeIds {t : Tree} {e : Entry} (he : e ∈ t.entries) :
    e.id ∈ t.nodeIds := by
  induction t with
  | empty => simp [entries] at he
  | node n l r il ir =>
    simp only [entries, List.mem_append] at he
    rcases he with (hn | hl) | hr
    · cases hp : n.peer <;> simp [NodeData.entries, NodeData.own, hp] at hn
      subst e
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (il hl))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ir hr))

theorem residentLists_filtered {d out : WG.Device} {t4 t6 : Tree}
    (h : ResidentLists d t4 t6) (ids : List Nat)
    (hm : ∀ pid : Nat, out.peers[pid]? = (d.peers[pid]?).map (unlistIds ids)) :
    ResidentLists out (t4.eraseIds ids) (t6.eraseIds ids) := by
  intro pid p hp
  rw [hm] at hp
  obtain ⟨old, hold, rfl⟩ := Option.map_eq_some_iff.mp hp
  obtain ⟨hn, hc⟩ := h pid old hold
  refine ⟨hn.filter _, ?_⟩
  intro id
  simp only [unlistIds, List.mem_filter, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
    Tree.eraseIds_entries, ← List.filter_append]
  constructor
  · rintro ⟨hi, hnot⟩
    obtain ⟨e, he, hid, hp⟩ := (hc id).mp hi
    exact ⟨e, ⟨he, by simpa [hid] using hnot⟩, hid, hp⟩
  · rintro ⟨e, ⟨he, hnot⟩, hid, hp⟩
    exact ⟨(hc id).mpr ⟨e, he, hid, hp⟩, by simpa [hid] using hnot⟩

def OwnedIds (ids : List Nat) (t4 t6 : Tree) : Prop :=
  ∀ id ∈ ids, ∃ e ∈ t4.entries ++ t6.entries, e.id = id

theorem OwnedIds.member {id : Nat} (h : OwnedIds ids t4 t6) (hi : id ∈ ids) :
    id ∈ t4.nodeIds ++ t6.nodeIds := by
  obtain ⟨e, he, rfl⟩ := h id hi
  rcases List.mem_append.mp he with he | he
  · exact List.mem_append_left _ (Tree.entry_mem_nodeIds he)
  · exact List.mem_append_right _ (Tree.entry_mem_nodeIds he)

theorem OwnedIds.tail {id : Nat} (h : OwnedIds (id :: ids) t4 t6) (hn : (id :: ids).Nodup) :
    OwnedIds ids (t4.eraseId id) (t6.eraseId id) := by
  intro q hq
  obtain ⟨e, he, hid⟩ := h q (List.mem_cons_of_mem _ hq)
  refine ⟨e, ?_, hid⟩
  rw [Tree.eraseId_entries, Tree.eraseId_entries, ← List.filter_append]
  exact List.mem_filter.mpr ⟨he, by simp [hid]; intro heq; exact (List.nodup_cons.mp hn).1 (heq ▸ hq)⟩

end Leanux.Proofs.WG.AllowedIps
