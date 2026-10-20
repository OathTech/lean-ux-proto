import PairInsertMemory

namespace Binary.Pair.Index
open Leanux Leanux.WG

theorem UnlinkedEntry.next_ne_back {n o m b link previous next entry}
    (f : UnlinkedEntry n o m) (fields : NodeFields n o m b link previous next entry)
    (layout : Layout o) (storage : storageCheck n o=true) :
    f.link+o.next≠link+o.pprev := by
  have back : link-o.hash+16=link+o.pprev := by
    have := fields.valid
    rw [layout.hash,layout.pprev] at *
    omega
  rw [←back]
  simp only [UnlinkedEntry.link,layout.hash,layout.next,Nat.add_zero]
  simpa only [layout.hash] using entry_address_ne storage f.named fields.named
    (by rw [layout.entrySize]; decide) (by rw [layout.entrySize]; decide) (fun _ => by decide)

theorem UnlinkedEntry.back_ne_next {n o m b link previous next entry}
    (f : UnlinkedEntry n o m) (fields : NodeFields n o m b link previous next entry)
    (layout : Layout o) (storage : storageCheck n o=true) :
    f.link+o.pprev≠link+o.next := by
  have nextAddress : link-o.hash+8=link+o.next := by
    have := fields.valid
    rw [layout.hash,layout.next] at *
    omega
  rw [←nextAddress]
  simp only [UnlinkedEntry.link,layout.hash,layout.pprev,Nat.add_assoc]
  simpa only [layout.hash] using entry_address_ne storage f.named fields.named
    (by rw [layout.entrySize]; decide) (by rw [layout.entrySize]; decide) (fun _ => by decide)

namespace InsertFocus

theorem firstFields {n o m} (f : InsertFocus n o m) (nonzero : head f.nodes≠0) :
    ∃ entry next, NodeFields n o m (f.index%8192) (head f.nodes) f.root next entry := by
  cases shape : f.nodes with
  | nil => simp [shape,head] at nonzero
  | cons node rest =>
    have chain := f.shape
    rw [shape] at chain
    cases chain with
    | cons fields tail => exact ⟨_,_,by simpa [shape,head,root] using fields⟩

theorem first_different {n o m} (f : InsertFocus n o m)
    (layout : Layout o) (table : 0<n.table) : head f.nodes≠f.fresh.link := by
  intro equal
  have nonzero : head f.nodes≠0 := equal ▸ f.fresh.nonzero layout
  have present : head f.nodes ∈ f.nodes.map Prod.fst := by
    cases h : f.nodes with
    | nil => simp [h,head] at nonzero
    | cons node rest => simp [head]
  exact f.fresh.absent layout table f.shape (equal ▸ present)

theorem root_ne_fresh {n o m} (f : InsertFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) :
    f.root≠f.fresh.link+o.next ∧ f.root≠f.fresh.link+o.pprev := by
  constructor
  · simpa only [root,UnlinkedEntry.link,layout.hash,layout.next,Nat.add_zero] using
      table_entry_ne layout storage f.fresh.named (offset := 8)
        (by rw [layout.entrySize]; decide) (Nat.mod_lt f.index (by decide))
  · simpa only [root,UnlinkedEntry.link,layout.hash,layout.pprev,Nat.add_assoc] using
      table_entry_ne layout storage f.fresh.named (offset := 16)
        (by rw [layout.entrySize]; decide) (Nat.mod_lt f.index (by decide))

theorem new_forward {n o m} (f : InsertFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (path : String) :
    word f.after path (f.fresh.link+o.next) 8=.ok (head f.nodes) := by
  rw [f.read_link layout storage _ (f.fresh.nextSlot layout),insertion_effect]
  have successor : ¬(head f.nodes≠0 ∧ f.fresh.link+o.next=head f.nodes+o.pprev) := by
    rintro ⟨nonzero,equal⟩
    obtain ⟨entry,next,fields⟩ := f.firstFields nonzero
    exact f.fresh.next_ne_back fields layout storage equal
  simp only [successor,Ne.symm (f.root_ne_fresh layout storage).1,↓reduceIte]

theorem new_back {n o m} (f : InsertFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (table : 0<n.table) (path : String) :
    word f.after path (f.fresh.link+o.pprev) 8=.ok f.root := by
  rw [f.read_link layout storage _ (f.fresh.backSlot layout),insertion_effect]
  have successor : ¬(head f.nodes≠0 ∧ f.fresh.link+o.pprev=head f.nodes+o.pprev) := by
    have := f.first_different layout table
    rintro ⟨_,equal⟩
    omega
  have next : f.fresh.link+o.pprev≠f.fresh.link+o.next := by rw [layout.pprev,layout.next]; omega
  simp only [successor,Ne.symm (f.root_ne_fresh layout storage).2,next,↓reduceIte]

theorem new_fields {n o m} (f : InsertFocus n o m)
    (validated : n.validate o=.ok ()) (storage : storageCheck n o=true) :
    NodeFields n o f.after (f.index%8192) f.fresh.link f.root (head f.nodes)
      ⟨f.index,f.fresh.owner⟩ := by
  obtain ⟨layout,_,addresses,_⟩ := validate_basic validated
  have base : f.fresh.link-o.hash=f.fresh.base := by simp only [UnlinkedEntry.link,Nat.add_sub_cancel]
  refine ⟨f.fresh.nonzero layout,by simp only [UnlinkedEntry.link]; omega,?_,?_,rfl,?_,
    f.new_back layout storage (validate_table_positive validated) _,f.new_forward layout storage _⟩
  · rw [base]
    exact ownerAt_of_named f.fresh.named addresses _
  · rw [base,f.read_data layout storage _ (by
      rw [layout.index]
      exact .entry _ _ 28 4 f.fresh.named (.inr (.inr rfl)))]
    exact word_path f.indexRead _
  · rw [base,f.read_data layout storage _ (by
      rw [layout.kind]
      exact .entry _ _ 24 4 f.fresh.named (.inr (.inl rfl)))]
    exact word_path f.kindRead _

#print axioms new_fields
end InsertFocus
end Binary.Pair.Index
