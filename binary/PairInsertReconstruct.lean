import PairInsertBucket
import PairKeyedDecode

namespace Binary.Pair.Index
open Leanux Leanux.WG

/-- Expose the record before projecting its fields. Direct reduction of an
Id-built target projection unnecessarily evaluates the 8192-bucket array. -/
theorem target_normal (d : Device) : target d={
    buckets := (List.range 8192).toArray.map (fun b => d.indexTable.filter (fun e => e.index%8192==b))
    ownerWords := (d.peers.toList.map (fun (id,p) => (IndexOwner.handshake id,p.handshakeEntryPeer))) ++
      (d.keypairs.toList.map (fun (id,k) => (IndexOwner.keypair id,k.peer)))
    refcounts := d.peers.toList.map (fun (id,p) => (id,p.refcount))} := rfl

theorem target_bucket_list (d : Device) : (target d).buckets.toList=
    (List.range 8192).map (fun b => d.indexTable.filter (fun e => e.index%8192==b)) := by
  simp only [target,Id.run,Pure.pure,Array.toList_map]

theorem target_index_owners (d : Device) (entries : List IndexEntry) :
    (target {d with indexTable := entries}).ownerWords=(target d).ownerWords := by
  rw [target_normal,target_normal]

theorem target_index_counts (d : Device) (entries : List IndexEntry) :
    (target {d with indexTable := entries}).refcounts=(target d).refcounts := by
  rw [target_normal,target_normal]

theorem InsertFocus.buckets_result {n o m d} (f : InsertFocus n o m)
    (related : Corresponds n o m d) (storage : storageCheck n o=true) :
    (List.range 8192).mapM (decodeBucket n o f.after)=.ok
      (target {d with indexTable := ⟨f.index,f.fresh.owner⟩::d.indexTable}).buckets.toList := by
  rw [target_bucket_list]
  apply IndexLookup.mapM_values
  intro b member
  have valid := List.mem_range.mp member
  have changed := f.decode_bucket (reconstruct_components related).1 storage valid (reconstruct_bucket related valid)
  by_cases same : b=f.index%8192
  · subst b
    simpa only [List.filter_cons,beq_self_eq_true,↓reduceIte] using changed
  · simpa only [List.filter_cons,beq_eq_false_iff_ne.mpr (Ne.symm same),
      Bool.false_eq_true,same,↓reduceIte] using changed

theorem InsertFocus.owners_frame {n o m} (f : InsertFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) :
    decodeOwners n o f.after=decodeOwners n o m := by
  apply Trie.mapM_same
  rintro ⟨owner,base⟩ named
  have read := f.read_data layout storage s!"owner[{repr owner}].peer"
    (DataSlot.entry owner base 0 8 named (.inl rfl))
  simp only [Nat.add_zero] at read
  simp only [layout.peer,Nat.add_zero,read]

theorem InsertFocus.counts_frame {n o m} (f : InsertFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) :
    decodeCounts n o f.after=decodeCounts n o m := by
  apply Trie.mapM_same
  rintro ⟨id,base⟩ named
  simp only [f.read_data layout storage _ (.count id base named)]

/-- hlist_add_head's concrete stores restore the unchanged executable
reconstruction at every bucket, retaining all owner peer words and counts. -/
theorem InsertFocus.reconstruct {n o m d} (f : InsertFocus n o m)
    (related : Corresponds n o m d) (storage : storageCheck n o=true) :
    Corresponds n o f.after {d with indexTable := ⟨f.index,f.fresh.owner⟩::d.indexTable} := by
  have parts := reconstruct_components related
  have layout := (validate_basic parts.1).1
  refine reconstruct_of_components (state := target {d with
    indexTable := ⟨f.index,f.fresh.owner⟩::d.indexTable}) parts.1 (f.buckets_result related storage) ?_ ?_
  · rw [target_index_owners,f.owners_frame layout storage]
    exact parts.2.2.1
  · rw [target_index_counts,f.counts_frame layout storage]
    exact parts.2.2.2

/-- Build the local shape from successful reconstruction and the resident
entry's current scalar fields; no future list or binary execution is supplied. -/
theorem insert_focus {n o m d index} (related : Corresponds n o m d)
    (fresh : UnlinkedEntry n o m)
    (indexRead : word m "insert.index" (fresh.base+o.index) 4=.ok index)
    (kindRead : word m "insert.kind" (fresh.base+o.kind) 4=.ok (ownerKind fresh.owner)) :
    ∃ f : InsertFocus n o m, f.fresh=fresh ∧ f.index=index := by
  have decoded := reconstruct_bucket related (Nat.mod_lt index (by decide))
  obtain ⟨first,read,run⟩ := bind_ok decoded
  obtain ⟨nodes,_,headEq,shape,_,distinct,_⟩ := bucket_shape run
  refine ⟨⟨fresh,index,indexRead,kindRead,nodes,shape,?_,distinct⟩,rfl,rfl⟩
  exact word_path (headEq ▸ read) _

#print axioms InsertFocus.reconstruct
#print axioms insert_focus
end Binary.Pair.Index
