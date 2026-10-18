import PairReplaceFocus

namespace Binary.Pair.Index.ReplaceFocus

theorem new_forward {n o m} (f : ReplaceFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (table : 0<n.table) (path : String) :
    word f.after path (f.link+o.next) 8=.ok f.old.next := by
  rw [f.read_link layout storage path (f.nextSlot layout),replacement_effect]
  have oldBack := f.next_ne_back layout storage f.old.fields
  have oldNext : f.link+o.next≠f.old.removed+o.next := by
    have := f.old_different layout table
    omega
  have successor : ¬(f.old.next≠0 ∧ f.link+o.next=f.old.next+o.pprev) := by
    rintro ⟨nonzero,equal⟩
    obtain ⟨entry,next,fields⟩ := f.old.nextFields nonzero
    exact f.next_ne_back layout storage fields equal
  have newBack : f.link+o.next≠f.link+o.pprev := by rw [layout.next,layout.pprev]; omega
  simp only [oldBack,oldNext,successor,Ne.symm (f.previous_different layout storage table),newBack,↓reduceIte]

theorem new_back {n o m} (f : ReplaceFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (table : 0<n.table) (path : String) :
    word f.after path (f.link+o.pprev) 8=.ok f.old.previous := by
  rw [f.read_link layout storage path (f.backSlot layout),replacement_effect]
  have oldBack : f.link+o.pprev≠f.old.removed+o.pprev := by
    have := f.old_different layout table
    omega
  have oldNext := Ne.symm (f.next_ne_newback layout storage f.old.fields)
  have successor : ¬(f.old.next≠0 ∧ f.link+o.pprev=f.old.next+o.pprev) := by
    have := f.next_different layout
    rintro ⟨_,equal⟩
    omega
  have previous := f.old.owner_back_ne_previous f.named layout storage
  change f.link+o.pprev≠f.old.previous at previous
  simp only [oldBack,oldNext,successor,previous,↓reduceIte]

theorem remaining_back {n o m b nodes link previous next entry} (f : ReplaceFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (bucket : b<8192)
    (shape : Chain n o m b (tableHead n o b) nodes) (member : (link,entry) ∈ nodes)
    (fields : NodeFields n o m b link previous next entry)
    (different : link≠f.old.removed) (newDifferent : link≠f.link) :
    word f.after s!"bucket[{b}].pprev" (link+o.pprev) 8=
      .ok (skip (f.old.removed+o.next) (f.link+o.next) previous) := by
  have neighbor := shape.neighbor_addresses member fields f.old.shape f.old.member f.old.fields
    (f.old.fields.root_ne_next layout storage bucket)
    (f.old.shape.predecessor_read f.old.member f.old.fields f.old.headRead)
  rw [f.read_link layout storage _ (fields.backSlot layout),replacement_effect]
  have oldBack : link+o.pprev≠f.old.removed+o.pprev := by omega
  have oldNext := Ne.symm (f.old.fields.next_ne_back fields layout storage)
  have prev := f.old.back_ne_previous fields layout storage
  have newBack : link+o.pprev≠f.link+o.pprev := by omega
  have newNext := Ne.symm (f.next_ne_back layout storage fields)
  have successor : (f.old.next≠0 ∧ link+o.pprev=f.old.next+o.pprev) ↔ previous=f.old.removed+o.next := by
    rw [neighbor.2]
    constructor
    · rintro ⟨_,equal⟩; omega
    · intro equal; exact ⟨equal ▸ fields.nonzero,by omega⟩
  simp only [oldBack,oldNext,successor,prev,newBack,newNext,fields.back,skip,↓reduceIte]
  split <;> rfl

theorem remaining_forward {n o m b nodes link previous next entry} (f : ReplaceFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (bucket : b<8192)
    (shape : Chain n o m b (tableHead n o b) nodes) (member : (link,entry) ∈ nodes)
    (fields : NodeFields n o m b link previous next entry)
    (different : link≠f.old.removed) (newDifferent : link≠f.link) :
    word f.after s!"bucket[{b}].next" (link+o.next) 8=.ok (skip f.old.removed f.link next) := by
  have neighbor := shape.neighbor_addresses member fields f.old.shape f.old.member f.old.fields
    (f.old.fields.root_ne_next layout storage bucket)
    (f.old.shape.predecessor_read f.old.member f.old.fields f.old.headRead)
  rw [f.read_link layout storage _ (fields.nextSlot layout),replacement_effect]
  have oldBack := fields.next_ne_back f.old.fields layout storage
  have oldNext : link+o.next≠f.old.removed+o.next := by omega
  have successor : ¬(f.old.next≠0 ∧ link+o.next=f.old.next+o.pprev) := by
    rintro ⟨nonzero,equal⟩
    obtain ⟨entry,next,successor⟩ := f.old.nextFields nonzero
    exact fields.next_ne_back successor layout storage equal
  have newBack := f.next_ne_newback layout storage fields
  have newNext : link+o.next≠f.link+o.next := by omega
  simp only [oldBack,oldNext,successor,←neighbor.1,newBack,newNext,fields.forward,skip,↓reduceIte]
  split <;> rfl

#print axioms new_forward
#print axioms new_back
#print axioms remaining_back
#print axioms remaining_forward
end Binary.Pair.Index.ReplaceFocus
