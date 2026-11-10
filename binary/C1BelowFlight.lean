import C1BelowReady
import SystemInvariant
import MemoryInvariant

/-! Result C1, work package 3: carrying `InFlight` through executed
instructions, and the byte-level separations `insertReady` gives. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-- Any execution keeps the direction flag and every readable range: the
two parts of `InFlight` no segment theorem states. -/
theorem eventually_flight {fetch : Int64 → Option Decoded} {a : MachineState}
    {P : MachineState → Prop} (run : Eventually (instructionStep fetch) P a) :
    Eventually (instructionStep fetch) (fun t => P t ∧
      MappedLe a.data.dmem t.data.dmem ∧ t.data.system.bits[10] = a.data.system.bits[10]) a := by
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (MemoryInvariant.eventually_mapped fetch (SystemInvariant.eventually_mode fetch run))
  rintro t ⟨⟨p,_,flag⟩,mapped⟩
  exact ⟨p,mapped,flag⟩

/-- `InFlight` at a later state from its parts. -/
theorem InFlight.later {L : Layout} {A : Allocator} {c : Context} {s a t : MachineState}
    (flight : InFlight L A c s a) (writes : BitVec 64 → Prop)
    (low : s.data.regs.rsp.toNat ≤ t.data.regs.rsp.toNat + insertWindow)
    (high : t.data.regs.rsp.toNat ≤ s.data.regs.rsp.toNat)
    (frame : EqualOutside writes a.data.dmem t.data.dmem)
    (inside : ∀ x, writes x → InsertWrites L A c s x)
    (mapped : MappedLe a.data.dmem t.data.dmem)
    (flag : t.data.system.bits[10] = a.data.system.bits[10])
    (coverage : c.At t.data.dmem) : InFlight L A c s t :=
  ⟨low,high,fun x unwritten => (flight.frame x unwritten).trans (frame x (fun h => unwritten (inside x h))),
    fun address size read => mapped address size (flight.mapped address size read),
    flag.trans flight.forward,coverage⟩

/-- A byte at a natural address inside the window below the entry's stack
pointer is scratch. -/
theorem scratch_nat {s : MachineState} {window : Nat} {a : BitVec 64}
    (low : s.data.regs.rsp.toNat ≤ a.toNat + window) (high : a.toNat < s.data.regs.rsp.toNat) :
    Scratch s window a := by
  refine ⟨window-(s.data.regs.rsp.toNat-a.toNat),by omega,?_⟩
  apply BitVec.eq_of_toNat_eq
  have bound := s.data.regs.rsp.toBitVec.isLt
  have small := a.isLt
  have rsp : s.data.regs.rsp.toBitVec.toNat = s.data.regs.rsp.toNat := rfl
  simp only [BitVec.toNat_add,BitVec.toNat_sub,BitVec.toNat_ofNat,rsp]
  omega

section Separation
variable {L : Layout} {A : Allocator} {c : Context} {s : MachineState} {family : Nat} {ra : UInt64}

/-- The stack window with the return word, as the caller's first span. -/
def Window (A : Allocator) (s : MachineState) (a : BitVec 64) : Prop :=
  InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)) (insertWindow + A.depth + 8) a

theorem window_span (A : Allocator) (s : MachineState) (a : BitVec 64) :
    Pair.Span.contains (ownWindow A s) a ↔ Window A s a := by
  simp only [ownWindow,Pair.Span.contains,Window,BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem scratch_window {a : BitVec 64} (scratch : Scratch s (insertWindow + A.depth) a) : Window A s a := by
  obtain ⟨i,bound,at_⟩ := scratch
  exact ⟨i,by omega,at_⟩

theorem ReadyFacts.heap_window (facts : ReadyFacts L A c s family ra) {a : BitVec 64}
    (heap : L.Heap a) : ¬Window A s a := by
  obtain ⟨span,member,inside⟩ := heap
  intro window
  exact spansApart_sound facts.heapApart member
    (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)) inside
    ((window_span A s a).mpr window)

theorem ReadyFacts.heap_cache (facts : ReadyFacts L A c s family ra) {a : BitVec 64}
    (heap : L.Heap a) : ¬InRange (.ofNat 64 cacheWord) 8 a := by
  obtain ⟨span,member,inside⟩ := heap
  exact spansApart_sound facts.heapApart member
    (r := (cacheWord,8)) (List.mem_append_left _ (List.mem_append_left _ (by simp))) inside

theorem ReadyFacts.heap_bytes (facts : ReadyFacts L A c s family ra) {a : BitVec 64}
    (heap : L.Heap a) : ¬c.bytes a := by
  obtain ⟨span,member,inside⟩ := heap
  intro read
  obtain ⟨other,named,within⟩ := Trie.readSpans_cover read
  exact spansApart_sound facts.heapApart member
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ named))))
    inside within

theorem ReadyFacts.heap_writes (facts : ReadyFacts L A c s family ra) {a : BitVec 64}
    (heap : L.Heap a) : ¬c.writes a := by
  obtain ⟨span,member,inside⟩ := heap
  intro written
  obtain ⟨other,named,within⟩ := Trie.writeSpans_cover written
  exact spansApart_sound facts.heapApart member
    (List.mem_append_right _ (List.mem_append_left _ named)) inside within

theorem ReadyFacts.bytes_window (facts : ReadyFacts L A c s family ra) {a : BitVec 64}
    (read : c.bytes a) : ¬Window A s a := by
  obtain ⟨span,named,within⟩ := Trie.readSpans_cover read
  intro window
  exact spansApart_sound facts.serviceStack
    (List.mem_append_left _ (List.mem_append_left _ named)) (List.mem_singleton_self _) within
    ((window_span A s a).mpr window)

theorem ReadyFacts.writes_window (facts : ReadyFacts L A c s family ra) {a : BitVec 64}
    (written : c.writes a) : ¬Window A s a := by
  obtain ⟨span,named,within⟩ := Trie.writeSpans_cover written
  intro window
  exact spansApart_sound facts.bufferApart (List.mem_append_left _ named)
    (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)) within
    ((window_span A s a).mpr window)

theorem ReadyFacts.writes_cache (facts : ReadyFacts L A c s family ra) {a : BitVec 64}
    (written : c.writes a) : ¬InRange (.ofNat 64 cacheWord) 8 a := by
  obtain ⟨span,named,within⟩ := Trie.writeSpans_cover written
  exact spansApart_sound facts.bufferApart (List.mem_append_left _ named)
    (r := (cacheWord,8)) (List.mem_append_left _ (List.mem_append_left _ (by simp))) within

theorem ReadyFacts.scratch_cache (facts : ReadyFacts L A c s family ra) {a : BitVec 64}
    (scratch : Scratch s (insertWindow + A.depth) a) : ¬InRange (.ofNat 64 cacheWord) 8 a := by
  refine spansApart_sound facts.callerApart (List.mem_singleton_self _)
    (r := (cacheWord,8)) (by simp) ?_
  simpa only [Pair.Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq,Scratch] using scratch

/-- Nothing an insertion may write touches the `node_cache` word. -/
theorem ReadyFacts.cache_kept (facts : ReadyFacts L A c s family ra) {a : BitVec 64}
    (cache : InRange (.ofNat 64 cacheWord) 8 a) : ¬InsertWrites L A c s a := by
  rintro (scratch|written|heap)
  · exact facts.scratch_cache scratch cache
  · exact facts.writes_cache written cache
  · exact facts.heap_cache heap cache

/-- The `node_cache` word still holds the cache at every state in flight. -/
theorem ReadyFacts.cache_read (facts : ReadyFacts L A c s family ra) {t : MachineState}
    (flight : InFlight L A c s t) : readNat t cacheWord 8 = .ok L.cache := by
  have kept : EqualOutside (InsertWrites L A c s) s.data.dmem t.data.dmem := flight.frame
  rw [←facts.cacheAt]
  unfold readNat
  rw [kept.loadBytes (.ofNat 64 cacheWord) 8 (fun i bound => facts.cache_kept ⟨i,bound,rfl⟩)]

end Separation

#print axioms ReadyFacts.cache_read
#print axioms ReadyFacts.heap_window
#print axioms InFlight.later
end Binary.Statements.C1.Proof
