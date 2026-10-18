import PairUnlinkFields

namespace Binary.Pair.Index
open Leanux Leanux.WG
local instance : LawfulBEq IndexOwner where
  eq_of_beq := by
    intro a b h
    cases a <;> cases b <;> simp_all [BEq.beq,instBEqIndexOwner.beq]
  rfl := by intro a; cases a <;> simp [BEq.beq,instBEqIndexOwner.beq]

theorem Chain.erase_entries {n o m b focusB root nodes removed previous next entry}
    (shape : Chain n o m b root nodes)
    (focus : NodeFields n o m focusB removed previous next entry)
    (unique : (n.owners.map Prod.fst).Nodup) :
    (Index.erase removed nodes).map Prod.snd = (nodes.map Prod.snd).filter (fun e => !(e.owner==entry.owner)) := by
  rw [List.filter_map]
  apply congrArg (List.map Prod.snd)
  apply List.filter_congr
  rintro ⟨link,current⟩ member
  obtain ⟨prev,next,fields⟩ := shape.member_fields member
  by_cases equal : link=removed
  · have owners := (fields.owner_iff focus unique).mpr equal
    simp only [Function.comp_apply,equal,owners,bne_self_eq_false,beq_self_eq_true,Bool.not_true]
  · have owners : current.owner≠entry.owner := fun h => equal ((fields.owner_iff focus unique).mp h)
    simp only [Function.comp_apply,show (link != removed)=true from by simpa using equal,
      show (current.owner==entry.owner)=false from beq_eq_false_iff_ne.mpr owners,Bool.not_false]

namespace UnlinkFocus

theorem read_head {n o m b nodes} (f : UnlinkFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (bucket : b<8192)
    (shape : Chain n o m b (tableHead n o b) nodes)
    (read : word m s!"bucket[{b}].head" (tableHead n o b) 8=.ok (head nodes)) :
    word (unlinkMemory m o f.removed f.previous f.next) s!"bucket[{b}].head" (tableHead n o b) 8=
      .ok (skip f.removed f.next (head nodes)) := by
  rw [f.read_link layout storage _ (.table b bucket)]
  have root_ne_back {current previous next entry bucket'}
      (fields : NodeFields n o m bucket' current previous next entry) : tableHead n o b≠current+o.pprev := by
    have address : current-o.hash+16=current+o.pprev := by
      have := fields.valid
      rw [layout.hash,layout.pprev] at *
      omega
    rw [←address]
    exact table_entry_ne layout storage fields.named (by rw [layout.entrySize]; decide) bucket
  have cleared := root_ne_back f.fields
  have successor : ¬(f.next≠0 ∧ tableHead n o b=f.next+o.pprev) := by
    rintro ⟨nonzero,equal⟩
    obtain ⟨entry,next,fields⟩ := f.nextFields nonzero
    exact root_ne_back fields equal
  have headEqual : tableHead n o b=f.previous ↔ head nodes=f.removed := by
    constructor
    · intro equal
      have headRead := read
      rw [equal] at headRead
      exact word_values headRead (f.shape.predecessor_read f.member f.fields f.headRead)
    · exact shape.head_back f.fields
  simp only [cleared,↓reduceIte,successor,headEqual,read,skip]
  split <;> rfl

theorem decode_bucket {n o m b entries} (f : UnlinkFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true)
    (unique : (n.owners.map Prod.fst).Nodup) (bucket : b<8192)
    (decoded : decodeBucket n o m b=.ok entries) :
    decodeBucket n o (unlinkMemory m o f.removed f.previous f.next) b=
      .ok (entries.filter (fun e => !(e.owner==f.entry.owner))) := by
  obtain ⟨first,headRead,run⟩ := bind_ok decoded
  obtain ⟨nodes,entriesEq,headEq,shape,updated⟩ := bucket_erase run f.fields (by
    intro nodes _ _ shape link entry prev next member different fields
    exact f.remaining_fields layout storage bucket shape member fields different)
  have newHead := f.read_head layout storage bucket shape (by simpa only [headEq] using headRead)
  have rootNe := f.fields.root_ne_next layout storage bucket
  have rootSkip : skip (f.removed+o.next) f.previous (tableHead n o b)=tableHead n o b := ite_eq_right rootNe
  rw [rootSkip] at updated
  unfold decodeBucket
  rw [newHead]
  change Binary.Pair.bucket n o _ b _ (skip f.removed f.next (head nodes)) (tableHead n o b) [] = _
  rw [←headEq,updated,shape.erase_entries f.fields unique,←entriesEq]

#print axioms decode_bucket
end UnlinkFocus
end Binary.Pair.Index
