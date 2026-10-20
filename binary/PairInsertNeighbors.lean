import PairInsertFields

namespace Binary.Pair.Index.InsertFocus
open Leanux Leanux.WG

theorem remaining_forward {n o m b nodes link previous next entry} (f : InsertFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (table : 0<n.table)
    (shape : Chain n o m b (tableHead n o b) nodes) (member : (link,entry) ∈ nodes)
    (fields : NodeFields n o m b link previous next entry) :
    word f.after s!"bucket[{b}].next" (link+o.next) 8=.ok next := by
  have different : link≠f.fresh.link := by
    intro same
    exact f.fresh.absent layout table shape (List.mem_map.mpr ⟨(link,entry),member,same⟩)
  have rootNe := fields.root_ne_next layout storage (Nat.mod_lt f.index (by decide))
  have backNe := Ne.symm (f.fresh.back_ne_next fields layout storage)
  have nextNe : link+o.next≠f.fresh.link+o.next := by omega
  have successor : ¬(head f.nodes≠0 ∧ link+o.next=head f.nodes+o.pprev) := by
    rintro ⟨nonzero,equal⟩
    obtain ⟨entry,next,firstFields⟩ := f.firstFields nonzero
    exact fields.next_ne_back firstFields layout storage equal
  rw [f.read_link layout storage _ (fields.nextSlot layout),insertion_effect]
  simp only [successor,Ne.symm rootNe,root,backNe,nextNe,fields.forward,↓reduceIte]

theorem remaining_back {n o m b nodes link previous next entry} (f : InsertFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (table : 0<n.table)
    (shape : Chain n o m b (tableHead n o b) nodes) (member : (link,entry) ∈ nodes)
    (read : word m "bucket.head" (tableHead n o b) 8=.ok (head nodes))
    (fields : NodeFields n o m b link previous next entry) :
    word f.after s!"bucket[{b}].pprev" (link+o.pprev) 8=
      .ok (skip f.root (f.fresh.link+o.next) previous) := by
  have different : link≠f.fresh.link := by
    intro same
    exact f.fresh.absent layout table shape (List.mem_map.mpr ⟨(link,entry),member,same⟩)
  have backAddress : link-o.hash+16=link+o.pprev := by
    have := fields.valid
    rw [layout.hash,layout.pprev] at *
    omega
  have rootNe : f.root≠link+o.pprev := by
    rw [←backAddress]
    exact table_entry_ne layout storage fields.named (by rw [layout.entrySize]; decide)
      (Nat.mod_lt f.index (by decide))
  have nextNe := Ne.symm (f.fresh.next_ne_back fields layout storage)
  have backNe : link+o.pprev≠f.fresh.link+o.pprev := by omega
  have successor : (head f.nodes≠0 ∧ link+o.pprev=head f.nodes+o.pprev) ↔ previous=f.root := by
    constructor
    · rintro ⟨_,equal⟩
      have atHead : head f.nodes=link := by omega
      exact (f.shape.head_back fields atHead).symm
    · intro equal
      have current := shape.predecessor_read member fields read
      rw [equal] at current
      have atHead := word_values current f.headRead
      exact ⟨atHead ▸ fields.nonzero,by omega⟩
  rw [f.read_link layout storage _ (fields.backSlot layout),insertion_effect]
  simp only [successor,Ne.symm rootNe,nextNe,backNe,fields.back,skip,↓reduceIte]
  split <;> rfl

theorem remaining_fields {n o m b nodes link previous next entry} (f : InsertFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (table : 0<n.table)
    (shape : Chain n o m b (tableHead n o b) nodes) (member : (link,entry) ∈ nodes)
    (read : word m "bucket.head" (tableHead n o b) 8=.ok (head nodes))
    (fields : NodeFields n o m b link previous next entry) :
    NodeFields n o f.after b link (skip f.root (f.fresh.link+o.next) previous) next entry := by
  refine ⟨fields.nonzero,fields.valid,fields.owner,?_,fields.bucket,?_,
    f.remaining_back layout storage table shape member read fields,
    f.remaining_forward layout storage table shape member fields⟩
  · rw [f.read_data layout storage _ (by
      rw [layout.index]
      exact .entry _ _ 28 4 fields.named (.inr (.inr rfl)))]
    exact fields.index
  · rw [f.read_data layout storage _ (by
      rw [layout.kind]
      exact .entry _ _ 24 4 fields.named (.inr (.inl rfl)))]
    exact fields.kind

#print axioms remaining_fields
end Binary.Pair.Index.InsertFocus
