import C1Interfaces
import PairAllowedipsHeapFrame
import PairAllowedipsFrame
import PairAllowedipsAssert

/-! Result C1, work package 1: the source side and the invariant's algebra. This module is the package's root in
`binary/lakefile.toml`. The brief is `binary/Statements/C1/proof/WP1.md`.

The package is this one file: the library lists its roots one by one, so a
module `C1SourceX` beside it is not a library module, and the lake file is
not the package's to edit. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1

/-- A sub-range of an object lies in any range that contains the object. -/
theorem inRange_widen {b a off size total : Nat} (lo : b ≤ a) (fits : a+off+size ≤ b+total)
    {x : BitVec 64} (inside : InRange (.ofNat 64 (a+off)) size x) :
    InRange (.ofNat 64 b) total x := by
  obtain ⟨i,hi,rfl⟩ := inside
  refine ⟨a-b+off+i,by omega,?_⟩
  rw [← BitVec.ofNat_add,← BitVec.ofNat_add]
  congr 1
  omega

theorem nodeFields_within : ∀ field ∈ nodeFields Root.nodeOffsets, field.1+field.2 ≤ nodeSize := by
  decide

/-- Every byte reconstruction reads is a heap byte. -/
theorem readSpans_heap {L : Layout} {names : Allowedips.Names}
    (table : names.table = L.table) (peers : names.trie.peers = L.peers)
    (arena : ∀ node ∈ names.trie.nodes, ∃ span ∈ L.arena, span.1 ≤ node.2 ∧ node.2+nodeSize ≤ span.1+span.2) :
    ∀ span ∈ readSpans names Root.nodeOffsets, ∀ a, span.contains a → L.Heap a := by
  intro span member a inside
  unfold readSpans at member
  rw [table,peers] at member
  rcases List.mem_append.mp member with tablePart | rest
  · exact ⟨span,List.mem_append_left _ (List.mem_append_left _ tablePart),inside⟩
  rcases List.mem_append.mp rest with nodePart | peerPart
  · obtain ⟨⟨id,base⟩,named,field⟩ := List.mem_flatMap.mp nodePart
    obtain ⟨⟨offset,size⟩,listed,rfl⟩ := List.mem_map.mp field
    obtain ⟨object,inArena,low,high⟩ := arena (id,base) named
    have bound := nodeFields_within (offset,size) listed
    refine ⟨object,List.mem_append_right _ inArena,?_⟩
    exact inRange_widen (total := object.2) low (by simp only at bound low high ⊢; omega) inside
  · exact ⟨span,List.mem_append_left _ (List.mem_append_right _ peerPart),inside⟩

theorem metadataSpans_subset (names : Allowedips.Names) (o : AllowedipsProbe.Offsets) :
    ∀ span ∈ metadataSpans names o, span ∈ readSpans names o := by
  intro span member
  unfold metadataSpans at member
  unfold readSpans
  rcases List.mem_append.mp member with tablePart | rest
  · exact List.mem_append_left _ tablePart
  rcases List.mem_append.mp rest with nodePart | peerPart
  · exact List.mem_append_right _ (List.mem_append_left _ nodePart)
  · obtain ⟨⟨id,base⟩,named,field⟩ := List.mem_flatMap.mp peerPart
    obtain ⟨⟨offset,size⟩,listed,rfl⟩ := List.mem_map.mp field
    refine List.mem_append_right _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨(id,base),named,List.mem_map.mpr ⟨(offset,size),?_,rfl⟩⟩))
    simp only [listFields,peerFields,List.mem_cons,List.not_mem_nil,or_false] at listed ⊢
    exact Or.inr listed

/-- The relation's decidable part and `Idle` across a change outside the heap. -/
theorem related_frame {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator}
    (contract : AllocatorContract fetch L A) {w : World} {m m' : Mem 64}
    (related : Related L A w m) (same : ∀ a, L.Heap a → m.get? a = m'.get? a) :
    Related L A w m' := by
  obtain ⟨names,stream,table,peers,asserted,armed,hidden,sites,apart,arena,idle⟩ := related
  have outside : EqualOutside (fun a => ¬L.Heap a) m m' := by
    intro a notWritten
    exact same a (Classical.not_not.mp notWritten)
  have reads : ∀ span ∈ readSpans names Root.nodeOffsets, ∀ a, span.contains a → ¬¬L.Heap a :=
    fun span member a inside => not_not_intro (readSpans_heap table peers arena span member a inside)
  obtain ⟨d,device,corresponds,shape⟩ := assertAt_ok asserted
  have corresponds' : Allowedips.Corresponds names Root.nodeOffsets m' d := by
    unfold Allowedips.Corresponds at corresponds ⊢
    rw [← reconstruct_frame names Root.nodeOffsets outside reads]
    exact corresponds
  have shape' : heap names (target d) m' = .ok () := by
    rw [← heap_frame names Root.nodeOffsets (target d) outside
      (fun span member => reads span (metadataSpans_subset names _ span member))]
    exact shape
  refine ⟨names,stream,table,peers,assertAt_of_related device corresponds' shape',armed,hidden,sites,
    apart,arena,contract.frame m m' _ _ idle ?_⟩
  intro a inArena _
  obtain ⟨span,member,inside⟩ := inArena
  exact same a ⟨span,List.mem_append_right _ member,inside⟩

theorem framedHolds : FramedHolds := by
  intro fetch L A premises w m m' related same
  exact related_frame premises.allocator related same

#print axioms framedHolds

end Binary.Statements.C1.Proof
