import Leanux.Proofs.WG.AllowedIps.RemovalLists

/-! Identifier-level entry effects of pure insertion. These supply the bridge
between source list updates and the prefix-based insertion specification. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

theorem NodeData.mem_entries_id {n : NodeData} {e : Entry} (he : e ∈ n.entries) : e.id = n.id := by
  cases hp : n.peer <;> simp [NodeData.entries, NodeData.own, hp] at he
  subst e
  rfl

theorem Tree.insertFresh_binding_origin (t : Tree) (width fresh addr cidr pid : Nat) :
    let ins := t.insertFresh width fresh addr cidr pid
    (ins.allocations = 0 ∧ ins.binding.id ∈ t.nodeIds) ∨
      (ins.allocations ≠ 0 ∧ ins.binding.id = fresh) := by
  induction t with
  | empty => exact .inr ⟨by change 1 ≠ 0; decide, rfl⟩
  | node n l r il ir =>
    rw [Tree.insertFresh]
    split
    · split
      · exact .inl ⟨rfl, List.mem_cons_self⟩
      · split
        · rcases il with ⟨ha, hi⟩ | h
          · exact .inl ⟨ha, List.mem_cons_of_mem _ (List.mem_append_left _ hi)⟩
          · exact .inr h
        · rcases ir with ⟨ha, hi⟩ | h
          · exact .inl ⟨ha, List.mem_cons_of_mem _ (List.mem_append_right _ hi)⟩
          · exact .inr h
    · right
      have ha := graft_allocations width fresh addr cidr pid (.node n l r)
      exact ⟨by omega, by rw [graft_binding]; rfl⟩

theorem Tree.insertFresh_binding_avoids (t : Tree) (width fresh addr cidr pid q : Nat)
    (hq : q ∉ t.nodeIds) (hb : q < fresh) :
    (t.insertFresh width fresh addr cidr pid).binding.id ≠ q := by
  rcases t.insertFresh_binding_origin width fresh addr cidr pid with ⟨_, hi⟩ | ⟨_, hi⟩
  · intro he
    exact hq (he ▸ hi)
  · omega

/-- Existing entries survive exactly when their node ID is not the updated
binding ID; the new binding is present even if the old node was ownerless. -/
theorem Tree.insertFresh_entries_id (t : Tree) (width fresh addr cidr pid : Nat)
    (hn : t.nodeIds.Nodup) (hf : ∀ q ∈ t.nodeIds, q < fresh) (e : Entry) :
    e ∈ (t.insertFresh width fresh addr cidr pid).tree.entries ↔
      e = (t.insertFresh width fresh addr cidr pid).binding ∨
        (e ∈ t.entries ∧ e.id ≠ (t.insertFresh width fresh addr cidr pid).binding.id) := by
  induction t with
  | empty => simp [Tree.insertFresh, graft, requestedLeaf, Tree.entries]
  | node n l r il ir =>
    obtain ⟨hnroot, hnchildren⟩ := List.nodup_cons.mp hn
    obtain ⟨hnl, hnr, hdis⟩ := List.nodup_append.mp hnchildren
    have hfl : ∀ q ∈ l.nodeIds, q < fresh := fun q hq => hf q (List.mem_cons_of_mem _ (List.mem_append_left _ hq))
    have hfr : ∀ q ∈ r.nodeIds, q < fresh := fun q hq => hf q (List.mem_cons_of_mem _ (List.mem_append_right _ hq))
    have hfn := hf n.id List.mem_cons_self
    have hnlroot : n.id ∉ l.nodeIds := fun h => hnroot (List.mem_append_left _ h)
    have hnrroot : n.id ∉ r.nodeIds := fun h => hnroot (List.mem_append_right _ h)
    have hel : ∀ e ∈ l.entries, e.id ≠ n.id := fun e he h => hnlroot (h ▸ Tree.entry_mem_nodeIds he)
    have her : ∀ e ∈ r.entries, e.id ≠ n.id := fun e he h => hnrroot (h ▸ Tree.entry_mem_nodeIds he)
    rw [Tree.insertFresh]
    split
    · split
      · have own : ({n with peer := some pid} : NodeData).entries = [n.entry pid] := rfl
        have ho : ∀ e ∈ n.entries, e.id = n.id := fun _ he => NodeData.mem_entries_id he
        simp only [Tree.entries, own, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        change _ ↔ e = n.entry pid ∨ ((_ ∨ _) ∧ e.id ≠ n.id)
        grind
      · split
        · have hi := il hnl hfl
          have hbn := l.insertFresh_binding_avoids width fresh addr cidr pid n.id hnlroot hfn
          have hbr : ∀ e ∈ r.entries, e.id ≠ (l.insertFresh width fresh addr cidr pid).binding.id := by
            intro e he
            have hid := Tree.entry_mem_nodeIds he
            have hnid : e.id ∉ l.nodeIds := fun hl => hdis _ hl _ hid rfl
            exact Ne.symm (l.insertFresh_binding_avoids width fresh addr cidr pid e.id hnid (hfr _ hid))
          have hbo : ∀ e ∈ n.entries, e.id ≠ (l.insertFresh width fresh addr cidr pid).binding.id := by
            intro e he
            rw [NodeData.mem_entries_id he]
            exact Ne.symm hbn
          simp only [Tree.entries, List.mem_append, hi]
          grind
        · have hi := ir hnr hfr
          have hbn := r.insertFresh_binding_avoids width fresh addr cidr pid n.id hnrroot hfn
          have hbl : ∀ e ∈ l.entries, e.id ≠ (r.insertFresh width fresh addr cidr pid).binding.id := by
            intro e he
            have hid := Tree.entry_mem_nodeIds he
            have hnid : e.id ∉ r.nodeIds := fun hr => hdis _ hid _ hr rfl
            exact Ne.symm (r.insertFresh_binding_avoids width fresh addr cidr pid e.id hnid (hfl _ hid))
          have hbo : ∀ e ∈ n.entries, e.id ≠ (r.insertFresh width fresh addr cidr pid).binding.id := by
            intro e he
            rw [NodeData.mem_entries_id he]
            exact Ne.symm hbn
          simp only [Tree.entries, List.mem_append, hi]
          grind
    · have hne : ∀ e ∈ (Tree.node n l r).entries, e.id ≠ fresh := by
        intro e he
        exact Nat.ne_of_lt (hf _ (Tree.entry_mem_nodeIds he))
      have he := (graft_entries width fresh addr cidr pid (.node n l r)).mem_iff (a := e)
      rw [graft_binding]
      rw [he, List.mem_cons]
      change (e = requestedEntry fresh addr cidr pid ∨ e ∈ (Tree.node n l r).entries) ↔
        e = requestedEntry fresh addr cidr pid ∨ (e ∈ (Tree.node n l r).entries ∧ e.id ≠ fresh)
      exact ⟨fun h => h.elim Or.inl (fun hm => .inr ⟨hm, hne e hm⟩),
        fun h => h.elim Or.inl (fun hm => .inr hm.1)⟩

end Leanux.Proofs.WG.AllowedIps
