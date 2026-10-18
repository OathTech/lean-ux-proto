import PairLookupPre

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG TrustBase LookupRelation CommonBitsCoverage Index
set_option maxRecDepth 2048

theorem CallFacts.data_cover {n o coverage s w d query kinds ra}
    (facts : CallFacts n o coverage s w d query kinds ra) :
    Covers (ownerSpans n ++ countSpans n o)
      (LookupDataWrites (callConfig n w d query kinds) (callView (callConfig n w d query kinds) d)) := by
  rintro a (owner | ⟨_,count⟩)
  · exact (owner_cover facts.related facts.names).append_left a owner
  · exact (count_cover facts.related).append_right a count

/-- Remove the caller/service part of a write footprint when framing a
retained heap field. Only possible index-data writes remain to be checked. -/
theorem CallFacts.heap_frame {n o coverage s w d query kinds ra after}
    (facts : CallFacts n o coverage s w d query kinds ra)
    (frame : EqualOutside (LookupWrites (callConfig n w d query kinds) coverage.coverage coverage.preempt s.data
      (callView (callConfig n w d query kinds) d)) s.data.dmem after)
    {a : BitVec 64} (heap : HeapBytes n o a)
    (data : ¬LookupDataWrites (callConfig n w d query kinds) (callView (callConfig n w d query kinds) d) a) :
    s.data.dmem.get? a=after.get? a := by
  apply frame a
  rintro (stack | buffer | preempt | written | ⟨needed,output⟩)
  · exact facts.frame.geometry.heap_external a heap (.inl stack)
  · exact facts.frame.geometry.heap_external a heap (.inr (.inl (coverage_writes buffer)))
  · exact facts.frame.geometry.heap_external a heap (.inr (.inr preempt))
  · exact data written
  · exact facts.output_heap needed a output heap

def SpansFrame (spans : List Span) (before after : DataMem) : Prop :=
  ∀ span ∈ spans, ∀ a, span.contains a → before.get? a=after.get? a

theorem SpansFrame.word {spans before after} (frame : SpansFrame spans before after)
    {span : Span} (member : span ∈ spans) (offset width : Nat) (within : offset+width≤span.2) (path : String) :
    word before path (span.1+offset) width=word after path (span.1+offset) width := by
  have reads : before.loadBytes (.ofNat 64 (span.1+offset)) width=after.loadBytes (.ofNat 64 (span.1+offset)) width := by
    unfold Mem.loadBytes
    congr 1
    apply List.map_congr_left
    intro i bound
    exact frame span member _ (span_slice within ⟨i,List.mem_range.mp bound,rfl⟩)
  unfold Binary.Pair.word
  rw [reads]

theorem CallFacts.shape_frame {n o coverage s w d query kinds ra after}
    (facts : CallFacts n o coverage s w d query kinds ra)
    (frame : EqualOutside (LookupWrites (callConfig n w d query kinds) coverage.coverage coverage.preempt s.data
      (callView (callConfig n w d query kinds) d)) s.data.dmem after) :
    SpansFrame (shapeSpans n o) s.data.dmem after := by
  have layout := (validate_basic (reconstruct_components facts.related).1).1
  intro span member a inside
  apply facts.heap_frame frame (shape_heap layout ⟨span,member,inside⟩)
  intro written
  obtain ⟨data,named,contains⟩ := facts.data_cover a written
  exact spansApart_sound facts.shapeApart named member contains inside

theorem SpansFrame.fields {n o before after b link previous next entry}
    (frame : SpansFrame (shapeSpans n o) before after) (layout : Layout o)
    (fields : NodeFields n o before b link previous next entry) :
    NodeFields n o after b link previous next entry := by
  let base := link-o.hash
  have member : (base+8,24) ∈ shapeSpans n o :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(entry.owner,base),fields.named,rfl⟩)
  have same := frame.word member
  have baseLink : base+8=link := by have := fields.valid; dsimp [base]; rw [layout.hash] at *; omega
  refine ⟨fields.nonzero,fields.valid,fields.owner,?_,fields.bucket,?_,?_,?_⟩
  · have read := same 20 4 (by omega) s!"bucket[{b}].index"
    have address : (base+8)+20=link-o.hash+o.index := by simp [base,layout.index,Nat.add_assoc]
    dsimp only at read
    rw [address] at read
    exact read.symm.trans fields.index
  · have read := same 16 4 (by omega) s!"bucket[{b}].kind"
    have address : (base+8)+16=link-o.hash+o.kind := by simp [base,layout.kind,Nat.add_assoc]
    dsimp only at read
    rw [address] at read
    exact read.symm.trans fields.kind
  · have read := same 8 8 (by omega) s!"bucket[{b}].pprev"
    have address : (base+8)+8=link+o.pprev := by rw [baseLink,layout.pprev]
    dsimp only at read
    rw [address] at read
    exact read.symm.trans fields.back
  · have read := same 0 8 (by omega) s!"bucket[{b}].next"
    have address : (base+8)+0=link+o.next := by simp [baseLink,layout.next]
    dsimp only at read
    rw [address] at read
    exact read.symm.trans fields.forward

theorem SpansFrame.bucket {n o before after b entries}
    (frame : SpansFrame (shapeSpans n o) before after) (layout : Layout o)
    (valid : b<8192) (decoded : decodeBucket n o before b=.ok entries) : decodeBucket n o after b=.ok entries := by
  obtain ⟨first,read,run⟩ := bind_ok decoded
  obtain ⟨nodes,entriesEq,headEq,shape,length,distinct,fresh⟩ := bucket_shape run
  have updated := (shape.frame (fun _ _ _ _ _ fields => frame.fields layout fields)).decode
    (n.owners.length+1) [] length distinct fresh
  rw [←entriesEq,←headEq] at updated
  have same := frame.word (List.mem_cons_self : (n.table,o.tableSize) ∈ shapeSpans n o)
    (o.buckets+b*o.headSize+o.first) 8 (by rw [layout.buckets,layout.headSize,layout.first,layout.tableSize]; omega)
    s!"bucket[{b}].head"
  have address : n.table+(o.buckets+b*o.headSize+o.first)=tableHead n o b := by unfold tableHead; omega
  rw [address] at same
  unfold decodeBucket
  rw [←same,read]
  exact updated

#print axioms CallFacts.shape_frame
#print axioms SpansFrame.bucket
end Binary.Pair.IndexLookup
