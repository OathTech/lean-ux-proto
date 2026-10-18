import PairReplaceFields

namespace Binary.Pair.Index
open Leanux Leanux.WG
local instance : LawfulBEq IndexOwner where
  eq_of_beq := by intro a b h; cases a <;> cases b <;> simp_all [BEq.beq,instBEqIndexOwner.beq]
  rfl := by intro a; cases a <;> simp [BEq.beq,instBEqIndexOwner.beq]

theorem entry_eq {a b : IndexEntry} (index : a.index=b.index) (owner : a.owner=b.owner) : a=b := by
  cases a; cases b; cases index; cases owner; rfl

namespace ReplaceFocus

theorem old_previous_ne_self {n o m} (f : ReplaceFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) : f.old.previous≠f.old.removed+o.next := by
  rcases f.old.shape.back_origin f.old.member f.old.fields with ⟨atRoot,_⟩ | ⟨parent,current,prev,_,address,fields⟩
  · rw [atRoot]
    exact f.old.fields.root_ne_next layout storage f.old.validBucket
  · rw [←address]
    intro equal
    have same : parent=f.old.removed := by omega
    subst parent
    have next := word_values f.old.fields.forward fields.forward
    exact f.old.shape.next_ne_self f.old.member f.old.fields next

theorem updated_fields {n o m b nodes link previous next entry} (f : ReplaceFocus n o m)
    (validated : n.validate o=.ok ()) (storage : storageCheck n o=true) (bucket : b<8192)
    (shape : Chain n o m b (tableHead n o b) nodes) (member : (link,entry) ∈ nodes)
    (fields : NodeFields n o m b link previous next entry) :
    NodeFields n o f.after b (skip f.old.removed f.link link)
      (skip (f.old.removed+o.next) (f.link+o.next) previous) (skip f.old.removed f.link next)
      (replaceOwner f.old.entry.owner f.newOwner entry) := by
  obtain ⟨layout,unique,_,_⟩ := validate_basic validated
  have table := validate_table_positive validated
  by_cases same : link=f.old.removed
  · subst link
    have index := word_values fields.index f.old.fields.index
    have owner := (fields.owner_iff f.old.fields unique).mpr rfl
    have equal := entry_eq index owner
    have sameBucket : b=f.old.bucket := fields.bucket.symm.trans (index ▸ f.old.fields.bucket)
    have previousEq := word_values fields.back f.old.fields.back
    have nextEq := word_values fields.forward f.old.fields.forward
    rw [equal,sameBucket,previousEq,nextEq]
    simpa only [skip,replaceOwner,beq_self_eq_true,↓reduceIte,
      f.old_previous_ne_self layout storage,f.old.shape.next_ne_self f.old.member f.old.fields]
      using f.new_fields validated storage
  · have ownerNe : entry.owner≠f.old.entry.owner := fun equal => same ((fields.owner_iff f.old.fields unique).mp equal)
    have newDifferent : link≠f.link := by
      intro equal
      exact f.absent layout table shape (List.mem_map.mpr ⟨(link,entry),member,equal⟩)
    simpa only [skip,same,↓reduceIte,replaceOwner,beq_eq_false_iff_ne.mpr ownerNe,Bool.false_eq_true]
      using f.remaining_fields layout storage bucket shape member fields same newDifferent

theorem read_head {n o m b nodes} (f : ReplaceFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (bucket : b<8192)
    (shape : Chain n o m b (tableHead n o b) nodes)
    (read : word m s!"bucket[{b}].head" (tableHead n o b) 8=.ok (head nodes)) :
    word f.after s!"bucket[{b}].head" (tableHead n o b) 8=.ok (skip f.old.removed f.link (head nodes)) := by
  rw [f.read_link layout storage _ (.table b bucket),replacement_effect]
  have root_ne {owner base offset} (named : (owner,base) ∈ n.owners) (bound : offset<o.entrySize) :=
    table_entry_ne layout storage named bound bucket
  have oldBase : f.old.removed-o.hash+o.hash=f.old.removed := Nat.sub_add_cancel f.old.fields.valid
  have oldBack : tableHead n o b≠f.old.removed+o.pprev := by
    have apart := root_ne (offset := 16) f.old.fields.named (by rw [layout.entrySize]; decide)
    have addr : f.old.removed-o.hash+16=f.old.removed+o.pprev := by
      rw [layout.hash,layout.pprev] at *
      omega
    simpa only [addr] using apart
  have oldNext := f.old.fields.root_ne_next layout storage bucket
  have successor : ¬(f.old.next≠0 ∧ tableHead n o b=f.old.next+o.pprev) := by
    rintro ⟨nonzero,equal⟩
    obtain ⟨entry,next,fields⟩ := f.old.nextFields nonzero
    have apart := root_ne (offset := 16) fields.named (by rw [layout.entrySize]; decide)
    have addr : f.old.next-o.hash+16=f.old.next+o.pprev := by
      have := fields.valid
      rw [layout.hash,layout.pprev] at *
      omega
    exact apart (by simpa only [addr] using equal)
  have newBack : tableHead n o b≠f.link+o.pprev := by
    simpa only [link,layout.hash,layout.pprev,Nat.add_assoc] using
      root_ne (offset := 16) f.named (by rw [layout.entrySize]; decide)
  have newNext : tableHead n o b≠f.link+o.next := by
    simpa only [link,layout.hash,layout.next,Nat.add_zero] using
      root_ne (offset := 8) f.named (by rw [layout.entrySize]; decide)
  have headEqual : tableHead n o b=f.old.previous ↔ head nodes=f.old.removed := by
    constructor
    · intro equal
      have headRead := read
      rw [equal] at headRead
      exact word_values headRead (f.old.shape.predecessor_read f.old.member f.old.fields f.old.headRead)
    · exact shape.head_back f.old.fields
  simp only [oldBack,oldNext,successor,headEqual,newBack,newNext,read,skip,↓reduceIte]
  split <;> rfl

theorem decode_bucket {n o m b entries} (f : ReplaceFocus n o m)
    (validated : n.validate o=.ok ()) (storage : storageCheck n o=true) (bucket : b<8192)
    (decoded : decodeBucket n o m b=.ok entries) :
    decodeBucket n o f.after b=.ok (entries.map (replaceOwner f.old.entry.owner f.newOwner)) := by
  obtain ⟨layout,_,_,_⟩ := validate_basic validated
  obtain ⟨first,headRead,decoded⟩ := bind_ok decoded
  obtain ⟨nodes,entriesEq,headEq,shape,length,distinct,_⟩ := bucket_shape decoded
  have newShape := shape.replace f.old.fields.nonzero
    (fun _ _ _ _ member fields => f.updated_fields validated storage bucket shape member fields)
  have root := f.old.fields.root_ne_next layout storage bucket
  rw [show skip (f.old.removed+o.next) (f.link+o.next) (tableHead n o b)=tableHead n o b from ite_eq_right root] at newShape
  have newDistinct := replace_distinct (old := f.old.removed)
    (oldOwner := f.old.entry.owner) (newOwner := f.newOwner)
    distinct (f.absent layout (validate_table_positive validated) shape)
  have run := newShape.decode (n.owners.length+1) [] (by simpa only [replaceNodes,List.length_map] using length)
    newDistinct (by simp)
  rw [replace_head _ _ _ _ _ f.old.fields.nonzero,←headEq] at run
  have newHead := f.read_head layout storage bucket shape (by simpa only [headEq] using headRead)
  unfold decodeBucket
  rw [newHead]
  change Binary.Pair.bucket n o f.after b _ (skip f.old.removed f.link (head nodes)) _ [] = _
  rw [←headEq,run,entriesEq]
  simp only [replaceNodes,List.map_map,Function.comp_def]

#print axioms decode_bucket
end ReplaceFocus
end Binary.Pair.Index
