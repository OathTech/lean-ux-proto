import PairUnlinkBucket

namespace Binary.Pair.Index
open Leanux Leanux.WG

/-- The concrete combined store effect reestablishes the unchanged runtime
reconstruction, including all buckets, owner words and peer counts. -/
theorem UnlinkFocus.reconstruct {n o m d} (f : UnlinkFocus n o m)
    (related : Corresponds n o m d) (storage : storageCheck n o=true) :
    Corresponds n o (unlinkMemory m o f.removed f.previous f.next)
      {d with indexTable := d.indexTable.filter (fun e => !(e.owner==f.entry.owner))} := by
  have components := reconstruct_components related
  obtain ⟨layout,unique,_⟩ := validate_basic components.1
  apply reconstruct_remove related
  · intro b valid
    obtain ⟨entries,_,read⟩ := (mapM_ok components.2.1).left b (List.mem_range.mpr valid)
    rw [read]
    exact f.decode_bucket layout storage unique valid read
  · apply Trie.mapM_same
    rintro ⟨owner,base⟩ named
    have read := f.read_data layout storage s!"owner[{repr owner}].peer"
      (DataSlot.entry owner base 0 8 named (.inl rfl))
    simp only [Nat.add_zero] at read
    simp only [layout.peer,Nat.add_zero,read]
  · apply Trie.mapM_same
    rintro ⟨id,base⟩ named
    simp only [f.read_data layout storage _ (.count id base named)]

theorem mapM_map_ok {f : α → Except ε β} {g : α → β} {xs : List α}
    (run : xs.mapM f=.ok (xs.map g)) : ∀ x ∈ xs, f x=.ok (g x) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.mapM_cons] at run
    obtain ⟨value,read,run⟩ := bind_ok run
    obtain ⟨tail,rest,run⟩ := bind_ok run
    have equal : value::tail=g x::xs.map g := Except.ok.inj run
    obtain ⟨rfl,tailEq⟩ := List.cons.inj equal
    rw [tailEq] at rest
    intro y member
    rcases List.mem_cons.mp member with rfl | member
    · exact read
    · exact ih rest y member

theorem reconstruct_bucket {n o m d} (related : Corresponds n o m d) {b : Nat} (valid : b<8192) :
    decodeBucket n o m b=.ok (d.indexTable.filter (fun e => e.index%8192==b)) := by
  have decoded := (reconstruct_components related).2.1
  have values : (target d).buckets.toList =
      (List.range 8192).map (fun b => d.indexTable.filter (fun e => e.index%8192==b)) := by
    simp only [target,Id.run,Pure.pure,Array.toList_map]
  rw [values] at decoded
  exact mapM_map_ok decoded b (List.mem_range.mpr valid)

/-- Every source entry represented by the runtime reconstruction yields an
unlink focus in its actual physical bucket; no list shape is supplied. -/
theorem reconstruct_focus {n o m d entry} (related : Corresponds n o m d)
    (present : entry ∈ d.indexTable) : ∃ f : UnlinkFocus n o m, f.entry=entry := by
  let b := entry.index%8192
  have valid : b<8192 := Nat.mod_lt _ (by decide)
  have decoded := reconstruct_bucket related valid
  obtain ⟨first,headRead,run⟩ := bind_ok decoded
  obtain ⟨nodes,entriesEq,headEq,shape,_,_,_⟩ := bucket_shape run
  have member : entry ∈ nodes.map Prod.snd := by
    rw [←entriesEq]
    exact List.mem_filter.mpr ⟨present,by simp [b]⟩
  obtain ⟨⟨link,current⟩,inNodes,equal⟩ := List.mem_map.mp member
  change current=entry at equal
  subst current
  obtain ⟨prev,next,fields⟩ := shape.member_fields inNodes
  refine ⟨⟨b,valid,nodes,link,prev,next,entry,shape,inNodes,fields,?_⟩,rfl⟩
  rw [headEq] at headRead
  exact word_path headRead _

#print axioms UnlinkFocus.reconstruct
#print axioms reconstruct_focus
end Binary.Pair.Index
