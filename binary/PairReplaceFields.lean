import PairReplaceNeighbors

namespace Binary.Pair.Index
open Leanux Leanux.WG

theorem ownerAt_of_named {n : Names} {owner base} (named : (owner,base) ∈ n.owners)
    (unique : (n.owners.map Prod.snd).Nodup) (path : String) : ownerAt n path base=.ok owner := by
  unfold ownerAt
  cases found : n.owners.find? (·.2==base) with
  | none =>
    have absent := List.find?_eq_none.mp found (owner,base) named
    simp at absent
  | some pair =>
    have address : pair.2=base := by simpa using List.find?_some found
    have present := List.mem_of_find?_eq_some found
    have equal : pair.1=owner := unique_second unique (by rw [←address]; exact present) named
    simp only [equal]
    rfl

namespace ReplaceFocus

theorem kind_frame {n o m owner base} (f : ReplaceFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true)
    (named : (owner,base) ∈ n.owners) (path : String) :
    word f.after path (base+o.kind) 4=word m path (base+o.kind) 4 := by
  rw [layout.kind]
  exact replacement_data_frame f.old layout storage f.named rfl path
    (.entry owner base 24 4 named (.inr (.inl rfl)))
    (entry_address_ne storage named f.named (by rw [layout.entrySize]; decide)
      (by rw [layout.entrySize]; decide) (fun _ => by decide)) _

theorem index_frame {n o m b link previous next entry} (f : ReplaceFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true)
    (fields : NodeFields n o m b link previous next entry) (different : link≠f.link) (path : String) :
    word f.after path (link-o.hash+o.index) 4=word m path (link-o.hash+o.index) 4 := by
  rw [layout.index]
  have address : link-o.hash+28≠f.base+28 := by
    have := fields.valid
    change link≠f.base+o.hash at different
    omega
  exact replacement_data_frame f.old layout storage f.named rfl path
    (.entry entry.owner (link-o.hash) 28 4 fields.named (.inr (.inr rfl))) address _

theorem new_fields {n o m} (f : ReplaceFocus n o m)
    (validated : n.validate o=.ok ()) (storage : storageCheck n o=true) :
    NodeFields n o f.after f.old.bucket f.link f.old.previous f.old.next
      {f.old.entry with owner := f.newOwner} := by
  obtain ⟨layout,_,addresses,_⟩ := validate_basic validated
  have table := validate_table_positive validated
  have base : f.link-o.hash=f.base := by simp only [link,Nat.add_sub_cancel]
  refine ⟨f.nonzero layout,by simp only [link]; omega,?_,?_,f.old.fields.bucket,?_,
    f.new_back layout storage table _,f.new_forward layout storage table _⟩
  · rw [base]
    exact ownerAt_of_named f.named addresses _
  · rw [base,layout.index]
    exact replacement_index f.old layout storage f.named rfl _
  · rw [base,f.kind_frame layout storage f.named]
    exact word_path f.kind _

theorem remaining_fields {n o m b nodes link previous next entry} (f : ReplaceFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (bucket : b<8192)
    (shape : Chain n o m b (tableHead n o b) nodes) (member : (link,entry) ∈ nodes)
    (fields : NodeFields n o m b link previous next entry)
    (different : link≠f.old.removed) (newDifferent : link≠f.link) :
    NodeFields n o f.after b link (skip (f.old.removed+o.next) (f.link+o.next) previous)
      (skip f.old.removed f.link next) entry := by
  refine ⟨fields.nonzero,fields.valid,fields.owner,?_,fields.bucket,?_,
    f.remaining_back layout storage bucket shape member fields different newDifferent,
    f.remaining_forward layout storage bucket shape member fields different newDifferent⟩
  · rw [f.index_frame layout storage fields newDifferent]
    exact fields.index
  · rw [f.kind_frame layout storage fields.named]
    exact fields.kind

#print axioms new_fields
#print axioms remaining_fields
end ReplaceFocus
end Binary.Pair.Index
