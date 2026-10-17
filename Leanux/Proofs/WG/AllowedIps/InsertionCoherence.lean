import Leanux.Proofs.WG.AllowedIps.InsertionDispatch
import Leanux.Proofs.WG.AllowedIps.InsertionEntries

/-! Resident-list coherence from actual represented input stores. Fresh append
normalizes to move-to-tail only after fresh-ID absence has been derived. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux

theorem ResidentLists.swap {d : WG.Device} {a b : Tree} (h : ResidentLists d a b) :
    ResidentLists d b a := by
  intro pid p hp
  obtain ⟨hn, he⟩ := h pid p hp
  refine ⟨hn, ?_⟩
  intro id
  simpa only [List.mem_append, or_comm] using he id

theorem resident_list_ids_below {d : WG.Device} {a b : Tree} {wa wb pid id : Nat}
    {pa pb : WG.Slot} {p : WG.Peer} (h : ResidentLists d a b)
    (ha : RepAt d.nodes wa pa a) (hb : RepAt d.nodes wb pb b)
    (hf : NodesBelow d) (hp : d.peers[pid]? = some p) (hi : id ∈ p.allowedipsList) :
    id < d.nextNode := by
  obtain ⟨e, he, rfl, _⟩ := ((h pid p hp).2 id).mp hi
  rcases List.mem_append.mp he with he | he
  · exact ha.ids_below hf _ (Tree.entry_mem_nodeIds he)
  · exact hb.ids_below hf _ (Tree.entry_mem_nodeIds he)

theorem unlist_of_absent (p : WG.Peer) (id : Nat) (hi : id ∉ p.allowedipsList) :
    unlist id p = p := by
  have hfilter : WG.listRemove p.allowedipsList id = p.allowedipsList := by
    apply List.filter_eq_self.mpr
    intro q hq
    simp only [bne_iff_ne]
    exact fun he => hi (he ▸ hq)
  simp only [unlist, hfilter]

theorem insertionPeer_zero_mem (p : WG.Peer) (binding pid q id : Nat) :
    id ∈ (insertionPeer 0 binding pid q p).allowedipsList ↔
      (id ∈ p.allowedipsList ∧ id ≠ binding) ∨ (id = binding ∧ q = pid) := by
  by_cases hq : q = pid <;>
    simp [insertionPeer, hq, unlist, WG.listRemove, List.mem_append]

theorem insertionPeer_zero_nodup (p : WG.Peer) (binding pid q : Nat)
    (hn : p.allowedipsList.Nodup) :
    (insertionPeer 0 binding pid q p).allowedipsList.Nodup := by
  by_cases hq : q = pid
  · simp only [insertionPeer, ↓reduceIte, hq, unlist]
    apply List.nodup_append.mpr
    refine ⟨hn.filter _, by simp, ?_⟩
    intro a ha b hb he
    have hne : a ≠ binding := by simpa [WG.listRemove] using (List.mem_filter.mp ha).2
    have hb' : b = binding := by simpa using hb
    exact hne (he.trans hb')
  · simp only [insertionPeer, ↓reduceIte, ite_eq_right hq, unlist]
    exact hn.filter _

/-- Generic coherence transport for an exact binding-ID update. The premise is
entry membership, not output coherence; concrete insertion supplies it below. -/
theorem residentLists_binding_update {d out : WG.Device} {a b a' b' : Tree}
    (h : ResidentLists d a b) (binding : Entry)
    (he : ∀ e, e ∈ a'.entries ++ b'.entries ↔
      e = binding ∨ (e ∈ a.entries ++ b.entries ∧ e.id ≠ binding.id))
    (hm : ∀ q : Nat, out.peers[q]? =
      (d.peers[q]?).map (insertionPeer 0 binding.id binding.peer q)) :
    ResidentLists out a' b' := by
  intro q p hp
  rw [hm] at hp
  obtain ⟨old, hold, rfl⟩ := Option.map_eq_some_iff.mp hp
  obtain ⟨hn, hc⟩ := h q old hold
  refine ⟨insertionPeer_zero_nodup old binding.id binding.peer q hn, ?_⟩
  intro id
  rw [insertionPeer_zero_mem]
  constructor
  · rintro (⟨hi, hne⟩ | ⟨rfl, hq⟩)
    · obtain ⟨e, heold, hid, hpeer⟩ := (hc id).mp hi
      exact ⟨e, (he e).mpr (.inr ⟨heold, by simpa [hid] using hne⟩), hid, hpeer⟩
    · exact ⟨binding, (he binding).mpr (.inl rfl), rfl, hq.symm⟩
  · rintro ⟨e, henew, hid, hpeer⟩
    rcases (he e).mp henew with rfl | ⟨heold, hne⟩
    · exact .inr ⟨hid.symm, hpeer.symm⟩
    · exact .inl ⟨(hc id).mpr ⟨e, heold, hid, hpeer⟩, by simpa [hid] using hne⟩

theorem insertion_binding_avoids_other (d : WG.Device) (v4 : Bool) (t other : Tree)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) t)
    (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other)
    (hb : NodesBelow d) (addr cidr pid : Nat) :
    ∀ e ∈ other.entries, e.id ≠ (t.insertFresh (rootWidth v4) d.nextNode addr cidr pid).binding.id := by
  intro e he
  have hi := Tree.entry_mem_nodeIds he
  have hw : rootWidth v4 ≠ rootWidth (!v4) := by cases v4 <;> decide
  rcases t.insertFresh_binding_origin (rootWidth v4) d.nextNode addr cidr pid with ⟨_, ht⟩ | ⟨_, hf⟩
  · intro hid
    exact hr.disjoint_width ho hw _ ht (hid ▸ hi)
  · have := ho.ids_below hb _ hi
    omega

theorem Inserted.normalized_peers (h : Inserted d out v4 t other addr cidr pid)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) t)
    (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other)
    (hb : NodesBelow d) (hl : ResidentLists d t other) (q : Nat) :
    out.peers[q]? = (d.peers[q]?).map
      (insertionPeer 0 (t.insertFresh (rootWidth v4) d.nextNode addr cidr pid).binding.id pid q) := by
  rw [h.peers]
  cases hp : d.peers[q]? with
  | none => rfl
  | some p =>
    rcases t.insertFresh_binding_origin (rootWidth v4) d.nextNode addr cidr pid with ⟨hz, _⟩ | ⟨hn, hi⟩
    · rw [hz]
    · have hnot : d.nextNode ∉ p.allowedipsList := by
        intro hm
        exact Nat.lt_irrefl _ (resident_list_ids_below hl hr ho hb hp hm)
      simp [insertionPeer, hn, hi, unlist_of_absent p d.nextNode hnot]

theorem Inserted.coherent (h : Inserted d out v4 t other addr cidr pid)
    (hr : RepAt d.nodes (rootWidth v4) (rootSlot v4) t)
    (ho : RepAt d.nodes (rootWidth (!v4)) (rootSlot (!v4)) other)
    (hb : NodesBelow d) (hn : t.nodeIds.Nodup) (hl : ResidentLists d t other) :
    ResidentLists out (t.insertFresh (rootWidth v4) d.nextNode addr cidr pid).tree other := by
  apply residentLists_binding_update hl (t.insertFresh (rootWidth v4) d.nextNode addr cidr pid).binding
  · intro e
    have hid := t.insertFresh_entries_id (rootWidth v4) d.nextNode addr cidr pid hn (hr.ids_below hb) e
    have hother := insertion_binding_avoids_other d v4 t other hr ho hb addr cidr pid e
    simp only [List.mem_append, hid]
    grind only
  · rw [Tree.insertFresh_peer]
    exact h.normalized_peers hr ho hb hl

end Leanux.Proofs.WG.AllowedIps
