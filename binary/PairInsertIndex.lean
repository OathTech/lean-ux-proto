import PairInsertReconstruct

namespace Binary.Pair.Index
open Leanux Leanux.WG

namespace UnlinkedEntry
def afterDraw {n o m} (f : UnlinkedEntry n o m) (value : Nat) : DataMem :=
  write32 m (f.base+28) value

theorem draw_link {n o m} (f : UnlinkedEntry n o m) (value : Nat)
    (layout : Layout o) (storage : storageCheck n o=true) {address}
    (slot : LinkSlot n o address) (path : String) :
    word (f.afterDraw value) path address 8=word m path address 8 :=
  word_after_index m value layout storage f.named slot path

theorem draw_data {n o m} (f : UnlinkedEntry n o m) (value : Nat)
    (layout : Layout o) (storage : storageCheck n o=true) {address size}
    (slot : DataSlot n o address size) (different : address≠f.base+28) (path : String) :
    word (f.afterDraw value) path address size=word m path address size :=
  word_write32_frame _ _ _ _ _ _ (slot.disjoint_index layout storage f.named different)

theorem draw_fields {n o m b link previous next entry} (f : UnlinkedEntry n o m) (value : Nat)
    (layout : Layout o) (storage : storageCheck n o=true)
    (fields : NodeFields n o m b link previous next entry) (different : link≠f.link) :
    NodeFields n o (f.afterDraw value) b link previous next entry := by
  refine ⟨fields.nonzero,fields.valid,fields.owner,?_,fields.bucket,?_,?_,?_⟩
  · rw [layout.index,f.draw_data value layout storage
      (.entry entry.owner (link-o.hash) 28 4 fields.named (.inr (.inr rfl))) (by
        have := fields.valid
        change link≠f.base+o.hash at different
        omega)]
    simpa only [layout.index] using fields.index
  · rw [layout.kind,f.draw_data value layout storage
      (.entry entry.owner (link-o.hash) 24 4 fields.named (.inr (.inl rfl)))
      (entry_address_ne storage fields.named f.named (by rw [layout.entrySize]; decide)
        (by rw [layout.entrySize]; decide) (fun _ => by decide))]
    simpa only [layout.kind] using fields.kind
  · rw [f.draw_link value layout storage (fields.backSlot layout)]
    exact fields.back
  · rw [f.draw_link value layout storage (fields.nextSlot layout)]
    exact fields.forward

theorem draw_chain {n o m b previous nodes} (f : UnlinkedEntry n o m) (value : Nat)
    (layout : Layout o) (storage : storageCheck n o=true)
    (shape : Chain n o m b previous nodes) (absent : f.link ∉ nodes.map Prod.fst) :
    Chain n o (f.afterDraw value) b previous nodes := by
  induction shape with
  | nil previous => exact .nil _
  | @cons previous link entry rest fields tail ih =>
    have different : link≠f.link := by intro same; apply absent; simp [same]
    exact .cons (f.draw_fields value layout storage fields different)
      (ih (fun member => absent (by simpa using Or.inr member)))

theorem draw_bucket {n o m b entries} (f : UnlinkedEntry n o m) (value : Nat)
    (validated : n.validate o=.ok ()) (storage : storageCheck n o=true) (valid : b<8192)
    (decoded : decodeBucket n o m b=.ok entries) :
    decodeBucket n o (f.afterDraw value) b=.ok entries := by
  have layout := (validate_basic validated).1
  obtain ⟨first,read,run⟩ := bind_ok decoded
  obtain ⟨nodes,entriesEq,headEq,shape,length,distinct,_⟩ := bucket_shape run
  have updated := f.draw_chain value layout storage shape
    (f.absent layout (validate_table_positive validated) shape)
  unfold decodeBucket
  rw [f.draw_link value layout storage (.table b valid),read]
  change bucket n o (f.afterDraw value) b (n.owners.length+1) first (tableHead n o b) []=.ok entries
  simpa only [headEq,entriesEq] using updated.decode _ [] length distinct (by simp)

/-- A retry overwrites only the unlinked resident index. It is outside
the currently reconstructed table, and all other reconstructed words frame. -/
theorem draw_reconstruct {n o m d} (f : UnlinkedEntry n o m) (value : Nat)
    (related : Corresponds n o m d) (storage : storageCheck n o=true) :
    Corresponds n o (f.afterDraw value) d := by
  have parts := reconstruct_components related
  have layout := (validate_basic parts.1).1
  apply reconstruct_of_components parts.1
  · rw [target_bucket_list]
    apply IndexLookup.mapM_values
    intro b member
    exact f.draw_bucket value parts.1 storage (List.mem_range.mp member)
      (reconstruct_bucket related (List.mem_range.mp member))
  · have frame : decodeOwners n o (f.afterDraw value)=decodeOwners n o m := by
      apply Trie.mapM_same
      rintro ⟨owner,base⟩ named
      have wordFrame := f.draw_data value layout storage
        (.entry owner base 0 8 named (.inl rfl))
        (entry_address_ne storage named f.named (by rw [layout.entrySize]; decide)
          (by rw [layout.entrySize]; decide) (fun _ => by decide)) s!"owner[{repr owner}].peer"
      simp only [Nat.add_zero] at wordFrame
      simp only [layout.peer,Nat.add_zero,wordFrame]
    rw [frame]
    exact parts.2.2.1
  · have frame : decodeCounts n o (f.afterDraw value)=decodeCounts n o m := by
      apply Trie.mapM_same
      rintro ⟨id,base⟩ named
      simp only [f.draw_data value layout storage (.count id base named)
        (count_index_ne layout storage named f.named)]
    rw [frame]
    exact parts.2.2.2

#print axioms draw_reconstruct

def drawn {n o m} (f : UnlinkedEntry n o m) (value : Nat)
    (layout : Layout o) (storage : storageCheck n o=true) : UnlinkedEntry n o (f.afterDraw value) :=
  ⟨f.owner,f.base,f.named,
    (f.draw_link value layout storage (f.backSlot layout) "owner.pprev").trans f.unlinked⟩

theorem draw_focus {n o m d} (f : UnlinkedEntry n o m) (value : Nat)
    (related : Corresponds n o m d) (storage : storageCheck n o=true) (small : value<2^32)
    (kind : word m "insert.kind" (f.base+o.kind) 4=.ok (ownerKind f.owner)) :
    ∃ focus : InsertFocus n o (f.afterDraw value), focus.fresh.owner=f.owner ∧
      focus.fresh.base=f.base ∧ focus.index=value := by
  have layout := (validate_basic (reconstruct_components related).1).1
  have bounded := entry_bound storage f.named
  rw [layout.entrySize] at bounded
  let fresh := f.drawn value layout storage
  have indexRead : word (f.afterDraw value) "insert.index" (fresh.base+o.index) 4=.ok value := by
    change word (f.afterDraw value) "insert.index" (f.base+o.index) 4=.ok value
    rw [layout.index]
    exact word_write32_same _ _ _ _ (by omega) small
  have kindRead : word (f.afterDraw value) "insert.kind" (fresh.base+o.kind) 4=.ok (ownerKind fresh.owner) := by
    change word (f.afterDraw value) "insert.kind" (f.base+o.kind) 4=.ok (ownerKind f.owner)
    rw [layout.kind,f.draw_data value layout storage
      (.entry f.owner f.base 24 4 f.named (.inr (.inl rfl))) (by omega)]
    simpa only [layout.kind] using kind
  obtain ⟨focus,equal,index⟩ := insert_focus (f.draw_reconstruct value related storage) fresh indexRead kindRead
  exact ⟨focus,by rw [equal]; rfl,by rw [equal]; rfl,index⟩

#print axioms draw_focus
end UnlinkedEntry
end Binary.Pair.Index
