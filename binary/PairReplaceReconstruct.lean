import PairReplaceBucket

namespace Binary.Pair.Index
open Leanux Leanux.WG

theorem replaceOwner_index (old new : IndexOwner) (e : IndexEntry) :
    (replaceOwner old new e).index=e.index := by
  unfold replaceOwner
  split <;> rfl

theorem target_replace (d : Device) (old new : IndexOwner) :
    target {d with indexTable := d.indexTable.map (replaceOwner old new)} =
      {(target d) with buckets := (target d).buckets.map (List.map (replaceOwner old new))} := by
  unfold target
  dsimp only [Id.run,Bind.bind,Pure.pure]
  simp only [Array.map_map]
  congr 1
  apply Array.map_congr_left
  intro b _
  simp only [List.filter_map,Function.comp_def,replaceOwner_index]

theorem ReplaceFocus.reconstruct {n o m d} (f : ReplaceFocus n o m)
    (related : Corresponds n o m d) (storage : storageCheck n o=true) :
    Corresponds n o f.after {d with indexTable := d.indexTable.map (replaceOwner f.old.entry.owner f.newOwner)} := by
  have parts := reconstruct_components related
  have layout := (validate_basic parts.1).1
  have buckets : ∀ b < 8192, decodeBucket n o f.after b =
      (decodeBucket n o m b).map (List.map (replaceOwner f.old.entry.owner f.newOwner)) := by
    intro b valid
    obtain ⟨entries,_,read⟩ := (mapM_ok parts.2.1).left b (List.mem_range.mpr valid)
    rw [read]
    exact f.decode_bucket parts.1 storage valid read
  have owners : decodeOwners n o f.after=decodeOwners n o m := by
    apply Trie.mapM_same
    rintro ⟨owner,base⟩ named
    have read := replacement_data_frame f.old layout storage f.named rfl
      s!"owner[{repr owner}].peer" (DataSlot.entry owner base 0 8 named (.inl rfl))
      (entry_address_ne storage named f.named (by rw [layout.entrySize]; decide)
        (by rw [layout.entrySize]; decide) (fun _ => by decide)) f.old.entry.index
    simp only [Nat.add_zero] at read
    change word f.after _ base 8=word m _ base 8 at read
    simp only [layout.peer,Nat.add_zero,read]
  have counts : decodeCounts n o f.after=decodeCounts n o m := by
    apply Trie.mapM_same
    rintro ⟨id,base⟩ named
    have read := replacement_data_frame f.old layout storage f.named rfl s!"peer[{id}].refcount"
      (DataSlot.count id base named) (count_index_ne layout storage named f.named) f.old.entry.index
    change word f.after _ (base+o.peerRefcount) 4=word m _ (base+o.peerRefcount) 4 at read
    simp only [read]
  unfold Corresponds
  rw [reconstruct_map_buckets n o m f.after _ buckets owners counts,related]
  exact congrArg Except.ok (target_replace d f.old.entry.owner f.newOwner).symm

#print axioms ReplaceFocus.reconstruct
end Binary.Pair.Index
