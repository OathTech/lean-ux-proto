import PairLookupRelation
import PairLookupCheck
import PairIndexExternal

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG TrustBase LookupRelation Index
set_option maxRecDepth 2048

theorem owner_cover {n o m w d query kinds} (related : Corresponds n o m d)
    (names : interpretationCheck n=true) :
    Covers (ownerSpans n) (LookupOwnerBytes (callConfig n w d query kinds)) := by
  rintro a ⟨owner,focus,inside⟩
  obtain ⟨value,present⟩ := selected_word related focus
  obtain ⟨base,_,named,_,_⟩ := owner_named related present
  refine ⟨(base,8),List.mem_map.mpr ⟨(owner,base),named,rfl⟩,?_⟩
  simpa only [callConfig_owner,(interpretation_owner names named).1,Span.contains] using inside

set_option maxHeartbeats 2000000 in
theorem count_cover {n o m w d query kinds} (related : Corresponds n o m d) :
    Covers (countSpans n o) (LookupCountBytes (callConfig n w d query kinds)) := by
  rintro a ⟨id,focus,inside⟩
  obtain ⟨peer,present⟩ := call_peer (w := w) (query := query) (kinds := kinds) related focus
  obtain ⟨base,named,_⟩ := peer_named related present
  have validation := validate_basic (reconstruct_components related).1
  refine ⟨(base+o.peerRefcount,4),List.mem_map.mpr ⟨(id,base),named,rfl⟩,?_⟩
  change InRange (Trie.interpretation n.peers id+.ofNat 64 Layouts.peer_refcount) 4 a at inside
  simpa only [Trie.interpretation_of_mem validation.2.2.2.1 named,validation.1.peerRefcount,
    Span.contains,BitVec.ofNat_add] using inside

theorem bucket_cover {n o m w d query kinds} (related : Corresponds n o m d)
    (names : interpretationCheck n=true) :
    Covers (shapeSpans n o) (LookupBucketBytes (callConfig n w d query kinds) (callView (callConfig n w d query kinds) d)) := by
  have layout := (validate_basic (reconstruct_components related).1).1
  rintro a (root | ⟨e,member,inside⟩)
  · refine ⟨(n.table,o.tableSize),List.mem_cons_self,?_⟩
    change InRange (BitVec.ofNat 64 n.table+.ofNat 64 (8*(query%8192))) 8 a at root
    rw [←BitVec.ofNat_add] at root
    exact span_slice (by rw [layout.tableSize]; have := Nat.mod_lt query (show 0<8192 by decide); omega) root
  · have present : e ∈ d.indexTable := (List.mem_filter.mp member).1
    obtain ⟨f,entryEq⟩ := reconstruct_focus related present
    have named := f.fields.named
    rw [entryEq] at named
    let base := f.removed-o.hash
    refine ⟨(base+8,24),List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(e.owner,base),named,rfl⟩),?_⟩
    have address : ownerAddress (callConfig n w d query kinds) e.owner=.ofNat 64 base :=
      (interpretation_owner names named).1
    rcases inside with next | kind | index
    · rw [address] at next
      have next : InRange (.ofNat 64 base+8#64) 8 a := next
      have shifted : InRange (.ofNat 64 (base+8)) 8 a := by simpa only [BitVec.ofNat_add] using next
      obtain ⟨i,hi,eq⟩ := shifted
      exact ⟨i,by omega,eq⟩
    · rw [address] at kind
      have shifted : InRange (.ofNat 64 ((base+8)+16)) 4 a := by
        simpa only [show base+8+16=base+24 by omega,BitVec.ofNat_add] using (show InRange (.ofNat 64 base+24#64) 4 a from kind)
      exact span_slice (by decide : 16+4≤24) shifted
    · rw [address] at index
      have shifted : InRange (.ofNat 64 ((base+8)+20)) 4 a := by
        simpa only [show base+8+20=base+28 by omega,BitVec.ofNat_add] using (show InRange (.ofNat 64 base+28#64) 4 a from index)
      exact span_slice (by decide : 20+4≤24) shifted

theorem owner_heap {n o a} (layout : Layout o) (covered : ∃ span ∈ ownerSpans n, span.contains a) : HeapBytes n o a := by
  obtain ⟨span,member,inside⟩ := covered
  obtain ⟨⟨owner,base⟩,named,rfl⟩ := List.mem_map.mp member
  have slot : DataSlot n o (base+0) 8 := .entry owner base 0 8 named (.inl rfl)
  exact slot.heap layout a (by simpa only [Nat.add_zero,Span.contains] using inside)

theorem count_heap {n o a} (layout : Layout o) (covered : ∃ span ∈ countSpans n o, span.contains a) : HeapBytes n o a := by
  obtain ⟨span,member,inside⟩ := covered
  obtain ⟨⟨id,base⟩,named,rfl⟩ := List.mem_map.mp member
  exact (DataSlot.count id base named).heap layout a inside

theorem shape_heap {n o a} (layout : Layout o) (covered : ∃ span ∈ shapeSpans n o, span.contains a) : HeapBytes n o a := by
  obtain ⟨span,member,inside⟩ := covered
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨_,table_storage n o,inside⟩
  · obtain ⟨⟨owner,base⟩,named,rfl⟩ := List.mem_map.mp member
    exact ⟨_,entry_storage named,span_slice (by rw [layout.entrySize]; exact (by decide : 8+24≤32)) inside⟩

theorem reads_heap {n o m w d query kinds} (related : Corresponds n o m d)
    (names : interpretationCheck n=true) :
    ∀ a, Reads (callConfig n w d query kinds) (callView (callConfig n w d query kinds) d) a → HeapBytes n o a := by
  have layout := (validate_basic (reconstruct_components related).1).1
  intro a read
  rcases read with root | node | owner | count
  · exact shape_heap layout (bucket_cover related names a (.inl root))
  · exact shape_heap layout (bucket_cover related names a (.inr node))
  · exact owner_heap layout (owner_cover related names a owner)
  · exact count_heap layout (count_cover related a count)

theorem data_heap {n o m w d query kinds} (related : Corresponds n o m d)
    (names : interpretationCheck n=true) : ∀ a,
    LookupDataWrites (callConfig n w d query kinds) (callView (callConfig n w d query kinds) d) a → HeapBytes n o a := by
  have layout := (validate_basic (reconstruct_components related).1).1
  rintro a (owner | ⟨_,count⟩)
  · exact owner_heap layout (owner_cover related names a owner)
  · exact count_heap layout (count_cover related a count)

#print axioms reads_heap
end Binary.Pair.IndexLookup
