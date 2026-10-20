import PairUnlinkReconstruct
import PairRemove

namespace Binary.Pair.Index
open Leanux Leanux.WG

/-- Byte equality on a finite storage cover, derived from an execution's
write footprint. This is a physical frame, not an additional observation. -/
def StorageFrame (n : Names) (o : Offsets) (before after : DataMem) : Prop :=
  ∀ span ∈ storageSpans n o, ∀ address, span.contains address → before.get? address=after.get? address

theorem StorageFrame.trans {n o first second third}
    (left : StorageFrame n o first second) (right : StorageFrame n o second third) :
    StorageFrame n o first third := fun span member a inside =>
  (left span member a inside).trans (right span member a inside)

theorem StorageFrame.loadInt {n o before after} (frame : StorageFrame n o before after)
    (base : BitVec 64) (width : Nat)
    (inside : ∀ a, InRange base width a → ∃ span ∈ storageSpans n o, span.contains a) :
    before.loadInt base width=after.loadInt base width := by
  have bytes : before.loadBytes base width=after.loadBytes base width := by
    unfold Mem.loadBytes
    congr 1
    apply List.map_congr_left
    intro i member
    obtain ⟨span,listed,read⟩ := inside (base+.ofNat 64 i) ⟨i,List.mem_range.mp member,rfl⟩
    exact frame span listed _ read
  rw [Mem.loadInt,bytes]
  rfl

theorem span_slice {base size offset width : Nat} {address : BitVec 64}
    (within : offset+width≤size) (inside : InRange (.ofNat 64 (base+offset)) width address) :
    InRange (.ofNat 64 base) size address := by
  obtain ⟨i,bound,equal⟩ := inside
  refine ⟨offset+i,by omega,?_⟩
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using equal

theorem StorageFrame.of_execution {n o before after writes}
    (frame : EqualOutside writes before after)
    (apart : ∀ span ∈ storageSpans n o, ∀ address, span.contains address → ¬writes address) :
    StorageFrame n o before after := fun span member address inside => frame address (apart span member address inside)

theorem StorageFrame.word {n o before after} (frame : StorageFrame n o before after)
    {span : Span} (member : span ∈ storageSpans n o) (offset width : Nat)
    (within : offset+width≤span.2) (path : String) :
    word before path (span.1+offset) width=word after path (span.1+offset) width := by
  have reads : before.loadBytes (.ofNat 64 (span.1+offset)) width=
      after.loadBytes (.ofNat 64 (span.1+offset)) width := by
    unfold Mem.loadBytes
    congr 1
    apply List.map_congr_left
    intro i index
    exact frame span member _ (span_slice within ⟨i,List.mem_range.mp index,rfl⟩)
  unfold Binary.Pair.word
  rw [reads]

theorem NodeFields.frame {n o before after b link previous next entry}
    (fields : NodeFields n o before b link previous next entry)
    (layout : Layout o) (frame : StorageFrame n o before after) :
    NodeFields n o after b link previous next entry := by
  have same := frame.word (entry_storage fields.named)
  have nextAddress : link-o.hash+8=link+o.next := by
    have := fields.valid
    rw [layout.hash,layout.next] at *
    omega
  have backAddress : link-o.hash+16=link+o.pprev := by
    have := fields.valid
    rw [layout.hash,layout.pprev] at *
    omega
  refine ⟨fields.nonzero,fields.valid,fields.owner,?_,fields.bucket,?_,?_,?_⟩
  · rw [←same o.index 4 (by rw [layout.index,layout.entrySize]; omega)]
    exact fields.index
  · rw [←same o.kind 4 (by rw [layout.kind,layout.entrySize]; omega)]
    exact fields.kind
  · rw [←backAddress,←same 16 8 (by rw [layout.entrySize]; omega),backAddress]
    exact fields.back
  · rw [←nextAddress,←same 8 8 (by rw [layout.entrySize]; omega),nextAddress]
    exact fields.forward

theorem StorageFrame.bucket {n o before after b entries} (frame : StorageFrame n o before after)
    (layout : Layout o) (valid : b<8192) (decoded : decodeBucket n o before b=.ok entries) :
    decodeBucket n o after b=.ok entries := by
  obtain ⟨first,read,run⟩ := bind_ok decoded
  obtain ⟨nodes,entriesEq,headEq,shape,length,distinct,fresh⟩ := bucket_shape run
  have updated := (shape.frame (fun _ _ _ _ _ fields => fields.frame layout frame)).decode
    (n.owners.length+1) [] length distinct fresh
  rw [←entriesEq,←headEq] at updated
  have headSame := frame.word (table_storage n o) (o.buckets+b*o.headSize+o.first) 8
    (by rw [layout.buckets,layout.headSize,layout.first,layout.tableSize]; omega) s!"bucket[{b}].head"
  have headAddress : n.table+(o.buckets+b*o.headSize+o.first)=tableHead n o b := by unfold tableHead; omega
  rw [headAddress] at headSame
  unfold decodeBucket
  rw [←headSame,read]
  exact updated

theorem StorageFrame.reconstruct {n o before after d} (frame : StorageFrame n o before after)
    (related : Corresponds n o before d) : Corresponds n o after d := by
  have components := reconstruct_components related
  have layout := (validate_basic components.1).1
  have buckets : ∀ b<8192, decodeBucket n o after b=(decodeBucket n o before b).map id := by
    intro b valid
    obtain ⟨entries,_,read⟩ := (mapM_ok components.2.1).left b (List.mem_range.mpr valid)
    rw [read]
    exact frame.bucket layout valid read
  have owners : decodeOwners n o after=decodeOwners n o before := by
    apply Trie.mapM_same
    rintro ⟨owner,base⟩ named
    dsimp only
    rw [←frame.word (entry_storage named) o.peer 8 (by rw [layout.peer,layout.entrySize]; omega)]
  have counts : decodeCounts n o after=decodeCounts n o before := by
    apply Trie.mapM_same
    rintro ⟨id,base⟩ named
    dsimp only
    have read := frame.word (count_storage named) 0 4 (by omega) s!"peer[{id}].refcount"
    simp only [Nat.add_zero] at read
    rw [←read]
  unfold Corresponds
  rw [reconstruct_map_buckets n o before after id buckets owners counts,related]
  simp only [Except.map,Array.map_id]

theorem StorageFrame.ownership {n o before after} (frame : StorageFrame n o before after)
    (layout : Layout o) : Remove.ownership n o before=Remove.ownership n o after := by
  apply Trie.mapM_same
  rintro ⟨owner,base⟩ named
  dsimp only
  have read := frame.word (entry_storage named) (o.hash+o.pprev) 8
    (by rw [layout.hash,layout.pprev,layout.entrySize]; omega) "owner.pprev"
  rw [←Nat.add_assoc] at read
  rw [read]

#print axioms StorageFrame.reconstruct
#print axioms StorageFrame.ownership
end Binary.Pair.Index
