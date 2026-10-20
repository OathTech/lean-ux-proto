import PairInsertNeighbors

namespace Binary.Pair.Index
open Leanux Leanux.WG

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

theorem Chain.length_le_owners {n o m b previous nodes}
    (shape : Chain n o m b previous nodes) (distinct : (nodes.map Prod.fst).Nodup) :
    nodes.length≤n.owners.length := by
  have subset : nodes.map Prod.fst ⊆ n.owners.map (fun p => p.2+o.hash) := by
    intro link member
    obtain ⟨⟨address,entry⟩,present,equal⟩ := List.mem_map.mp member
    obtain ⟨prev,next,fields⟩ := shape.member_fields present
    refine List.mem_map.mpr ⟨(entry.owner,address-o.hash),fields.named,?_⟩
    have := fields.valid
    change address=link at equal
    change address-o.hash+o.hash=link
    omega
  simpa only [List.length_map] using distinct.length_le_of_subset subset

namespace InsertFocus

theorem remaining_chain {n o m b nodes} (f : InsertFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (table : 0<n.table)
    (shape : Chain n o m b (tableHead n o b) nodes)
    (read : word m "bucket.head" (tableHead n o b) 8=.ok (head nodes)) :
    Chain n o f.after b (skip f.root (f.fresh.link+o.next) (tableHead n o b)) nodes := by
  have update : ∀ previous rest, Chain n o m b previous rest →
      (∀ node ∈ rest, node ∈ nodes) →
      Chain n o f.after b (skip f.root (f.fresh.link+o.next) previous) rest := by
    intro previous rest current
    induction current with
    | nil previous => intro _; exact .nil _
    | @cons previous link entry rest fields tail ih =>
      intro subset
      have first := f.remaining_fields layout storage table shape (subset _ (by simp)) read fields
      have remaining := ih (fun node member => subset node (by simp [member]))
      have apart := fields.root_ne_next layout storage (Nat.mod_lt f.index (by decide))
      have unchanged : skip f.root (f.fresh.link+o.next) (link+o.next)=link+o.next :=
        ite_eq_right (Ne.symm apart)
      rw [unchanged] at remaining
      exact .cons first remaining
  exact update _ _ shape (fun _ member => member)

theorem read_head {n o m b} (f : InsertFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (valid : b<8192) :
    word f.after s!"bucket[{b}].head" (tableHead n o b) 8=
      if b=f.index%8192 then .ok f.fresh.link else
        word m s!"bucket[{b}].head" (tableHead n o b) 8 := by
  have nextNe : tableHead n o b≠f.fresh.link+o.next := by
    simpa only [UnlinkedEntry.link,layout.hash,layout.next,Nat.add_zero] using
      table_entry_ne layout storage f.fresh.named (offset := 8) (by rw [layout.entrySize]; decide) valid
  have backNe : tableHead n o b≠f.fresh.link+o.pprev := by
    simpa only [UnlinkedEntry.link,layout.hash,layout.pprev,Nat.add_assoc] using
      table_entry_ne layout storage f.fresh.named (offset := 16) (by rw [layout.entrySize]; decide) valid
  have successor : ¬(head f.nodes≠0 ∧ tableHead n o b=head f.nodes+o.pprev) := by
    rintro ⟨nonzero,equal⟩
    obtain ⟨entry,next,fields⟩ := f.firstFields nonzero
    have address : head f.nodes-o.hash+16=head f.nodes+o.pprev := by
      have := fields.valid
      rw [layout.hash,layout.pprev] at *
      omega
    exact table_entry_ne (offset := 16) layout storage fields.named (by rw [layout.entrySize]; decide) valid
      (by simpa only [address] using equal)
  have rootEq : tableHead n o b=f.root ↔ b=f.index%8192 := by
    simp only [root,tableHead,layout.buckets,layout.headSize,layout.first]
    omega
  rw [f.read_link layout storage _ (.table b valid),insertion_effect]
  simp only [successor,nextNe,backNe,rootEq,↓reduceIte]

theorem original_bucket {n o m} (f : InsertFocus n o m) :
    decodeBucket n o m (f.index%8192)=.ok (f.nodes.map Prod.snd) := by
  unfold decodeBucket
  rw [word_path f.headRead _]
  exact f.shape.decode _ [] (by have := f.shape.length_le_owners f.distinct; omega)
    f.distinct (by simp)

theorem decode_bucket {n o m b entries} (f : InsertFocus n o m)
    (validated : n.validate o=.ok ()) (storage : storageCheck n o=true) (valid : b<8192)
    (decoded : decodeBucket n o m b=.ok entries) :
    decodeBucket n o f.after b=.ok (if b=f.index%8192 then ⟨f.index,f.fresh.owner⟩::entries else entries) := by
  obtain ⟨layout,_,_,_⟩ := validate_basic validated
  have table := validate_table_positive validated
  by_cases same : b=f.index%8192
  · subst b
    have entriesEq : f.nodes.map Prod.snd=entries := Except.ok.inj (f.original_bucket.symm.trans decoded)
    have tail := f.remaining_chain layout storage table f.shape f.headRead
    have changedRoot : skip f.root (f.fresh.link+o.next) f.root=f.fresh.link+o.next := by simp [skip]
    change Chain n o f.after (f.index%8192) (skip f.root (f.fresh.link+o.next) f.root) f.nodes at tail
    rw [changedRoot] at tail
    have newShape := Chain.cons (f.new_fields validated storage) tail
    have distinct : (((f.fresh.link,⟨f.index,f.fresh.owner⟩)::f.nodes).map Prod.fst).Nodup := by
      simp only [List.map_cons,List.nodup_cons]
      exact ⟨f.fresh.absent layout table f.shape,f.distinct⟩
    have decodedNew := newShape.decode (n.owners.length+1) [] (by
      have := f.shape.length_le_owners f.distinct
      simpa using Nat.succ_le_succ this) distinct (by simp)
    unfold decodeBucket
    rw [f.read_head layout storage (Nat.mod_lt f.index (by decide))]
    simpa only [↓reduceIte,ok_bind,head,root,List.head?_cons,Option.map_some,Option.getD_some,List.map_cons,entriesEq]
      using decodedNew
  · obtain ⟨first,read,run⟩ := bind_ok decoded
    obtain ⟨nodes,entriesEq,headEq,shape,length,distinct,_⟩ := bucket_shape run
    have rootNe : tableHead n o b≠f.root := by
      simp only [root,tableHead,layout.buckets,layout.headSize,layout.first]
      omega
    have updated := f.remaining_chain layout storage table shape (by
      simpa only [headEq] using word_path read "bucket.head")
    rw [show skip f.root (f.fresh.link+o.next) (tableHead n o b)=tableHead n o b from ite_eq_right rootNe] at updated
    unfold decodeBucket
    rw [f.read_head layout storage valid,ite_eq_right same,read]
    simpa only [ite_eq_right same,ok_bind,headEq,entriesEq] using updated.decode _ [] length distinct (by simp)

#print axioms decode_bucket
end InsertFocus
end Binary.Pair.Index
