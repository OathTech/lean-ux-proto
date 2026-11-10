import C1ServiceReady
import MemoryInvariant
import SystemInvariant
import PairFrameProof

/-! Result C1, work package 4: the two service rules (`AllocRule`, `FreeRule`),
derived from `AllocatorContract` and the caller's conditions. The mapping and
the direction flag across a service body are not promised by the contract:
they come from `MemoryInvariant.eventually_mapped` and
`SystemInvariant.eventually_mode`, which hold of any executed instructions. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-! ## Address arithmetic -/

private theorem sub_toNat (x : BitVec 64) (n : Nat) (h : n ≤ x.toNat) :
    (x - .ofNat 64 n).toNat = x.toNat - n := by
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

private theorem sub_bound (x : BitVec 64) (n : Nat)
    (h : (x - .ofNat 64 n).toNat + n + 8 ≤ 2^64) : n ≤ x.toNat := by
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat] at h
  omega

private theorem inRange_iff (base : BitVec 64) (n : Nat) (h : base.toNat + n ≤ 2^64) (a : BitVec 64) :
    InRange base n a ↔ base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + n := by
  constructor
  · rintro ⟨i,bound,rfl⟩
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rintro ⟨lower,upper⟩
    refine ⟨a.toNat - base.toNat,by omega,?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := a.isLt
    omega

/-- The stack geometry of an insertion in natural numbers: the window fits
below the stack pointer and the return word below the top of memory. -/
structure Geometry (A : Allocator) (s e : MachineState) : Prop where
  window : insertWindow + A.depth ≤ s.data.regs.rsp.toNat
  top : s.data.regs.rsp.toNat + 8 ≤ 2^64
  low : s.data.regs.rsp.toNat ≤ e.data.regs.rsp.toNat + insertWindow
  high : e.data.regs.rsp.toNat ≤ s.data.regs.rsp.toNat

private theorem table_heap (L : Layout) : (L.table+AllowedipsMutationLayout.root4,8) ∈ L.heap := by
  simp [Layout.heap, Layout.fixed, tableFields]

theorem Ready.geometry {L : Layout} {A : Allocator} {c : Context} {s e : MachineState}
    (ready : Ready L A c s) (low : s.data.regs.rsp.toNat ≤ e.data.regs.rsp.toNat + insertWindow)
    (high : e.data.regs.rsp.toNat ≤ s.data.regs.rsp.toNat) : Geometry A s e := by
  have checked := List.all_eq_true.mp (List.all_eq_true.mp ready.heapStack _ (table_heap L))
    (stackSpan A s) (by simp)
  have valid : (stackSpan A s).1 + (stackSpan A s).2 ≤ 2^64 := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
    exact checked.1.2
  simp only [stackSpan] at valid
  have window : insertWindow + A.depth ≤ s.data.regs.rsp.toNat :=
    sub_bound s.data.regs.rsp.toBitVec (insertWindow + A.depth) (by omega)
  have base : (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)).toNat =
      s.data.regs.rsp.toNat - (insertWindow + A.depth) := sub_toNat _ _ window
  rw [base] at valid
  exact ⟨window,by omega,low,high⟩

variable {L : Layout} {A : Allocator} {c : Context} {s e : MachineState}

private theorem scratch_entry (g : Geometry A s e) (a : BitVec 64) :
    Scratch s (insertWindow + A.depth) a ↔
      s.data.regs.rsp.toNat - (insertWindow + A.depth) ≤ a.toNat ∧ a.toNat < s.data.regs.rsp.toNat := by
  have window := g.window
  have base : (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)).toNat =
      s.data.regs.rsp.toNat - (insertWindow + A.depth) := sub_toNat _ _ window
  unfold Scratch
  rw [inRange_iff _ _ (by have := g.top; omega), base]
  omega

private theorem scratch_service (g : Geometry A s e) (a : BitVec 64) :
    Scratch e A.depth a ↔
      e.data.regs.rsp.toNat - A.depth ≤ a.toNat ∧ a.toNat < e.data.regs.rsp.toNat := by
  have window := g.window
  have low := g.low
  have high := g.high
  have top := g.top
  have base : (e.data.regs.rsp.toBitVec - .ofNat 64 A.depth).toNat = e.data.regs.rsp.toNat - A.depth :=
    sub_toNat _ _ (show A.depth ≤ e.data.regs.rsp.toNat by simp only [insertWindow] at *; omega)
  unfold Scratch
  rw [inRange_iff _ _ (by omega), base]
  omega

private theorem stack_contains (g : Geometry A s e) (a : BitVec 64) :
    (stackSpan A s).contains a ↔
      s.data.regs.rsp.toNat - (insertWindow + A.depth) ≤ a.toNat ∧ a.toNat < s.data.regs.rsp.toNat + 8 := by
  have window := g.window
  have top := g.top
  have base : (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)).toNat =
      s.data.regs.rsp.toNat - (insertWindow + A.depth) := sub_toNat _ _ window
  unfold Pair.Span.contains stackSpan
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [inRange_iff _ _ (by omega), base]
  omega

private theorem live_range (g : Geometry A s e) (a : BitVec 64) :
    InRange e.data.regs.rsp.toBitVec (s.data.regs.rsp.toNat + 8 - e.data.regs.rsp.toNat) a ↔
      e.data.regs.rsp.toNat ≤ a.toNat ∧ a.toNat < s.data.regs.rsp.toNat + 8 := by
  have high := g.high
  have top := g.top
  have same : e.data.regs.rsp.toBitVec.toNat = e.data.regs.rsp.toNat := rfl
  rw [inRange_iff _ _ (by omega), same]
  omega

/-- The service's scratch and its return word lie in the insertion's stack span. -/
theorem stack_of_service (g : Geometry A s e) {a : BitVec 64}
    (inside : Scratch e A.depth a ∨ InRange e.data.regs.rsp.toBitVec 8 a) :
    (stackSpan A s).contains a := by
  have low := g.low
  have high := g.high
  have window := g.window
  have top := g.top
  refine (stack_contains g a).mpr ?_
  rcases inside with scratch | word
  · have := (scratch_service g a).mp scratch
    simp only [insertWindow] at *
    omega
  · have same : e.data.regs.rsp.toBitVec.toNat = e.data.regs.rsp.toNat := rfl
    have := (inRange_iff _ _ (by omega) a).mp word
    simp only [insertWindow] at *
    omega

/-! ## Footprints -/

private theorem arena_heap {a : BitVec 64} (inside : L.Arena a) : L.Heap a := by
  obtain ⟨span,member,contains⟩ := inside
  exact ⟨span,by simp [Layout.heap, member],contains⟩

private theorem fixed_heap {a : BitVec 64} (inside : ∃ span ∈ L.fixed, span.contains a) : L.Heap a := by
  obtain ⟨span,member,contains⟩ := inside
  exact ⟨span,by simp [Layout.heap, member],contains⟩

private theorem kept_arena {kept : List Nat} (arena : ∀ node ∈ kept, InArena L node) {a : BitVec 64}
    (inside : Kept kept a) : L.Arena a := by
  obtain ⟨object,member,i,bound,rfl⟩ := inside
  obtain ⟨span,spanMember,lower,upper⟩ := arena object member
  refine ⟨span,spanMember,object - span.1 + i,by simp only [nodeSize] at upper bound; omega,?_⟩
  rw [←BitVec.ofNat_add, ←BitVec.ofNat_add]
  congr 1
  omega

private theorem within (base offset size total : Nat) (bound : offset + size ≤ total) {a : BitVec 64}
    (inside : Pair.Span.contains (base+offset,size) a) : Pair.Span.contains (base,total) a := by
  obtain ⟨i,small,rfl⟩ := inside
  refine ⟨offset+i,by omega,?_⟩
  simp only [BitVec.ofNat_add, BitVec.add_assoc]

/-- A table or peer word lies in the table or a peer as a whole object. -/
private theorem fixed_object {a : BitVec 64} (inside : ∃ span ∈ L.fixed, span.contains a) :
    ∃ span ∈ objectsOf L, span.contains a := by
  obtain ⟨span,member,contains⟩ := inside
  simp only [Layout.fixed, List.mem_append, List.mem_map, List.mem_flatMap] at member
  rcases member with ⟨⟨offset,size⟩,field,rfl⟩ | ⟨⟨id,address⟩,peer,⟨offset,size⟩,field,rfl⟩
  · refine ⟨(L.table,AllowedipsMutationLayout.tableSize),by simp [objectsOf],?_⟩
    simp only [tableFields, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at field
    rcases field with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> exact within _ _ _ _ (by decide) contains
  · refine ⟨(address,Layouts.peerSize),by
      simp only [objectsOf, List.mem_append, List.mem_map]
      exact .inr ⟨(id,address),peer,rfl⟩,?_⟩
    simp only [peerFields, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at field
    rcases field with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> exact within _ _ _ _ (by decide) contains

private theorem writes_buffer {a : BitVec 64} (write : c.writes a) :
    ∃ span ∈ Trie.callBuffers c, span.contains a := by
  obtain ⟨span,member,contains⟩ := Trie.writeSpans_cover write
  exact ⟨span,by simp [Trie.callBuffers, member],contains⟩

/-- The service's write set lies inside the insertion's. -/
theorem serviceWrites_insertWrites (g : Geometry A s e) (kept : List Nat) {a : BitVec 64}
    (write : ServiceWrites L A c e kept a) : InsertWrites L A c s a := by
  rcases write with scratch | ⟨arena,-⟩ | coverage
  · refine .inl ((scratch_entry g a).mpr ?_)
    have := (scratch_service g a).mp scratch
    have := g.low
    have := g.high
    have := g.window
    simp only [insertWindow] at *
    omega
  · exact .inr (.inr (arena_heap arena))
  · exact .inr (.inl coverage)

/-- No protected byte is in the service's write set. -/
theorem protected_apart (ready : Ready L A c s) (g : Geometry A s e)
    (objects : spansApart (objectsOf L) L.arena = true) {kept : List Nat}
    (arena : ∀ node ∈ kept, InArena L node) {a : BitVec 64}
    (inside : Protected L s e kept a) : ¬ServiceWrites L A c e kept a := by
  have low := g.low
  have high := g.high
  have window := g.window
  have scratchStack (scratch : Scratch e A.depth a) : (stackSpan A s).contains a := by
    have := (scratch_service g a).mp scratch
    refine (stack_contains g a).mpr ?_
    simp only [insertWindow] at *
    omega
  have heapStack (heap : L.Heap a) : ¬(stackSpan A s).contains a := by
    obtain ⟨span,member,contains⟩ := heap
    exact spansApart_sound ready.heapStack member (by simp) contains
  have heapWrites (heap : L.Heap a) : ¬c.writes a := by
    obtain ⟨span,member,contains⟩ := heap
    intro write
    obtain ⟨buffer,bufferMember,bufferContains⟩ := writes_buffer write
    exact spansApart_sound ready.heapBuffers member bufferMember contains bufferContains
  rcases inside with stack | fixed | kept | cache
  · have range := (live_range g a).mp stack
    have stackAt : (stackSpan A s).contains a := (stack_contains g a).mpr (by
      simp only [insertWindow] at *
      omega)
    rintro (scratch | ⟨heap,-⟩ | coverage)
    · have := (scratch_service g a).mp scratch
      omega
    · exact heapStack (arena_heap heap) stackAt
    · obtain ⟨buffer,member,contains⟩ := writes_buffer coverage
      exact spansApart_sound ready.buffersStack member (by simp) contains stackAt
  · rintro (scratch | ⟨heap,-⟩ | coverage)
    · exact heapStack (fixed_heap fixed) (scratchStack scratch)
    · obtain ⟨object,member,contains⟩ := fixed_object fixed
      obtain ⟨span,spanMember,spanContains⟩ := heap
      exact spansApart_sound objects member spanMember contains spanContains
    · exact heapWrites (fixed_heap fixed) coverage
  · have heap := arena_heap (kept_arena arena kept)
    rintro (scratch | ⟨-,free⟩ | coverage)
    · exact heapStack heap (scratchStack scratch)
    · exact free kept
    · exact heapWrites heap coverage
  · have cacheAt : Pair.Span.contains (cacheWord,8) a := cache
    rintro (scratch | ⟨heap,-⟩ | coverage)
    · have inWindow : Pair.Span.contains
          ((s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)).toNat, insertWindow + A.depth) a := by
        unfold Pair.Span.contains
        simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
        refine (scratch_entry g a).mpr ?_
        have := (scratch_service g a).mp scratch
        simp only [insertWindow] at *
        omega
      exact spansApart_sound ready.windowCache (by simp) (by simp) inWindow cacheAt
    · obtain ⟨span,member,contains⟩ := arena_heap heap
      exact spansApart_sound ready.heapCache member (by simp) contains cacheAt
    · obtain ⟨buffer,member,contains⟩ := writes_buffer coverage
      exact spansApart_sound ready.buffersCache member (by simp) contains cacheAt

/-! ## The service's entry and return -/

/-- `ServiceReady` at a service entry inside an insertion. -/
theorem serviceReady (ready : Ready L A c s) (flight : InFlight L A c s e) : ServiceReady A c e := by
  have g := ready.geometry flight.low flight.high
  refine ⟨flight.coverage,ready.capacity,flight.forward,?_⟩
  intro i bound
  have low := g.low
  have high := g.high
  have window := g.window
  have top := g.top
  let j := s.data.regs.rsp.toNat - e.data.regs.rsp.toNat + A.depth - i - 1
  have at_entry := ready.stack j (by simp only [j, insertWindow] at *; omega)
  have same : e.data.regs.rsp.toBitVec - .ofNat 64 A.depth + .ofNat 64 i =
      s.data.regs.rsp.toBitVec - .ofNat 64 (j+1) := by
    apply BitVec.eq_of_toNat_eq
    have left : (e.data.regs.rsp.toBitVec - .ofNat 64 A.depth).toNat = e.data.regs.rsp.toNat - A.depth :=
      sub_toNat _ _ (show A.depth ≤ e.data.regs.rsp.toNat by simp only [insertWindow] at *; omega)
    have right : (s.data.regs.rsp.toBitVec - .ofNat 64 (j+1)).toNat = s.data.regs.rsp.toNat - (j+1) :=
      sub_toNat _ _ (show j+1 ≤ s.data.regs.rsp.toNat by simp only [j, insertWindow] at *; omega)
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, left, right]
    simp only [j, insertWindow] at *
    omega
  rw [same]
  have read : (s.data.dmem.loadInt (s.data.regs.rsp.toBitVec - .ofNat 64 (j+1)) 1).isSome = true :=
    (loadInt_defined _ _ _).mpr (fun k small => by
      have zero : k = 0 := by omega
      subst zero
      simpa using at_entry)
  simpa using (loadInt_defined _ _ _).mp (flight.mapped _ _ read) 0 (by omega)

/-- The call is still in flight when a service returns. -/
theorem inFlight_returned (ready : Ready L A c s) (flight : InFlight L A c s e)
    (room : e.data.regs.rsp.toNat + 8 ≤ s.data.regs.rsp.toNat)
    {t : MachineState} {back : UInt64} {kept : List Nat}
    (returned : Returned e t back)
    (frame : EqualOutside (ServiceWrites L A c e kept) e.data.dmem t.data.dmem)
    (coverage : c.At t.data.dmem)
    (mapped : ∀ a n, (e.data.dmem.loadInt a n).isSome = true → (t.data.dmem.loadInt a n).isSome = true)
    (forward : t.data.system.bits[10] = e.data.system.bits[10]) : InFlight L A c s t := by
  have g := ready.geometry flight.low flight.high
  have top := g.top
  have low := g.low
  have stack : t.data.regs.rsp.toNat = e.data.regs.rsp.toNat + 8 := by
    rw [returned.2.1, UInt64.toNat_add]
    have : (8 : UInt64).toNat = 8 := rfl
    omega
  refine ⟨by omega,by omega,?_,?_,?_,coverage⟩
  · intro a outside
    rw [flight.frame a outside]
    exact frame a (fun write => outside (serviceWrites_insertWrites g kept write))
  · exact fun a n read => mapped a n (flight.mapped a n read)
  · rw [forward]
    exact flight.forward

/-! ## The rules -/

/-- ACCEPTANCE: the allocation rule. -/
theorem allocRule : AllocRule := by
  intro fetch L A premises c s e family key cidr pid ra back live record stream
    callReady objects arena flight room entry frame cache flags site idle
  have ready := ready_of_insertReady callReady
  have g := ready.geometry flight.low flight.high
  have run := premises.allocator.alloc c e back live record stream entry frame
    (serviceReady ready flight) cache flags site idle
  have run := SystemInvariant.eventually_mode fetch (MemoryInvariant.eventually_mapped fetch run)
  refine eventually_weaken _ _ _ _ ?_ run
  rintro t ⟨⟨⟨returned,equal,coverage,result⟩,mapped⟩,-,forward⟩
  refine ⟨returned,result,inFlight_returned ready flight room returned equal coverage mapped forward,?_⟩
  intro a inside
  exact (equal a (protected_apart ready g objects arena inside)).symm

/-- ACCEPTANCE: the release rule. -/
theorem freeRule : FreeRule := by
  intro fetch L A premises c s e family key cidr pid ra back live stream
    callReady objects arena flight room entry frame site cache object idle
  have ready := ready_of_insertReady callReady
  have g := ready.geometry flight.low flight.high
  have run := premises.allocator.free c e back live stream entry frame
    (serviceReady ready flight) site cache object idle
  have run := SystemInvariant.eventually_mode fetch (MemoryInvariant.eventually_mapped fetch run)
  refine eventually_weaken _ _ _ _ ?_ run
  rintro t ⟨⟨⟨returned,equal,coverage,result⟩,mapped⟩,-,forward⟩
  refine ⟨returned,result,inFlight_returned ready flight room returned equal coverage mapped forward,?_⟩
  intro a inside
  exact (equal a (protected_apart ready g objects
    (fun node member => arena node (List.mem_of_mem_erase member)) inside)).symm

#print axioms allocRule
#print axioms freeRule

end Binary.Statements.C1.Proof
