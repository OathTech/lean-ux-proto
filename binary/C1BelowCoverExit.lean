import C1BelowCoverLink
import C1BelowPrefixFinal
import C1BelowInv
import C1BelowSeq

/-! Result C1, work package 3, covering path: from the machine's state at
the common exit (either sub-case) to `AtExit`: in flight, the saved bytes,
the answer, the invariant for the mirror's final world, the sequence word. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase AllowedipsChild
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root
local instance : Labels := Image.linkedLabels

theorem node_heap {L : Layout} {address : Nat} (arena : InArena L address) {a : BitVec 64}
    (inside : InRange (.ofNat 64 address) 72 a) : L.Heap a :=
  arena_heap (offset:=0) arena (by decide) inside

/-- `ebx = 0` is the 32-bit answer zero. -/
theorem zero_answer (regs : Reg64s) (zero : regs.rbx=0) :
    regs.get (.low .rbx .W32)=BitVec.ofInt 32 0 := by
  simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,zero]

#print axioms zero_answer

/-- THE EXIT OF THE COVERING PATH, either sub-case. `x` is the machine at
`add+0x549`, reached from the comparison state `t` by writes inside the
locals, the node below, the fresh node, a third heap region `other` (the
parent node or the root slot) and the coverage calls' footprint; its memory
is related, under the names extended by the fresh node, to a device equal
to `step`'s up to `target`. -/
theorem cover_at_exit {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator}
    (premises : Premises fetch L A)
    {c : Context} {s : MachineState} {w w' : World} {family key cidr pid : Nat} {ra : UInt64}
    {answer : Int} {d : Device} {stream : List HiddenRecord} {placed : Option NodeId} {exact : Bool}
    {st : Step} {names : Allowedips.Names} {base : Nat} {e : MachineState}
    (inv : Inv L A w s.data.dmem)
    (ready : insertReady L A c s family key cidr pid ra=.ok ())
    (facts : StepFacts w family key cidr pid answer w' d stream placed exact st)
    (case : st.case = .cover) (answerZero : st.answer=0)
    (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e)
    (extra : CutExtra L s e family)
    {m : DataMem} {t x : MachineState}
    (compared : AtCompare L A c s e names base cidr stream m t)
    (stackT : t.data.regs.rsp=e.data.regs.rsp)
    {downId down : Nat} {other : BitVec 64 → Prop} {dev : Device}
    (downNamed : (downId,down) ∈ names.trie.nodes)
    (otherHeap : ∀ a, other a → L.Heap a)
    (otherKept : ∀ a, other a → L.Arena a → Kept (names.trie.nodes.map (·.2)++[base]) a)
    (pc : x.pc=Add.entry+0x549) (rbx : x.data.regs.rbx=0) (rsp : x.data.regs.rsp=t.data.regs.rsp)
    (calls : CallsReady c x.data)
    (frame : EqualOutside (C1Cover.PathWrites t.data c (.ofNat 64 down) (.ofNat 64 base) other)
      t.data.dmem x.data.dmem)
    (mapped : MappedLe t.data.dmem x.data.dmem)
    (flag : x.data.system.bits[10]=t.data.system.bits[10])
    (related : Corresponds (names.allocated base) nodeOffsets x.data.dmem dev)
    (shape : heap (names.allocated base) (Allowedips.target dev) x.data.dmem=.ok ())
    (deviceEq : Allowedips.target st.device=Allowedips.target dev)
    (seqEq : dev.peerAllowedips.seq=(bump d).peerAllowedips.seq) :
    AtExit L A c s e w' answer x := by
  have rfacts := ready_facts ready
  obtain ⟨fits,top⟩ := rfacts.window_bounds
  have high := extra.frameHigh
  have low := extra.frameLow
  unfold insertWindow at fits low
  have rspE : e.data.regs.rsp.toBitVec.toNat=e.data.regs.rsp.toNat := rfl
  have rspS : s.data.regs.rsp.toBitVec.toNat=s.data.regs.rsp.toNat := rfl
  have downArena : InArena L down := cut.arena _ downNamed
  have zoneWindow : ∀ a, Zone e.data.regs.rsp a → Window A s a :=
    fun a zone => scratch_window (zone_scratch_window rfacts extra zone)
  -- every written byte is scratch, coverage buffer or heap
  have inside : ∀ a, C1Cover.PathWrites t.data c (.ofNat 64 down) (.ofNat 64 base) other a →
      InsertWrites L A c s a := by
    rintro a (h|h|h|h|h|h)
    · rw [stackT] at h
      exact .inl (zone_scratch_window rfacts extra (zone_locals (by decide) h))
    · exact .inr (.inr (node_heap downArena h))
    · exact .inr (.inr (node_heap cut.fresh h))
    · exact .inr (.inr (otherHeap a h))
    · rw [stackT] at h
      exact .inl (zone_scratch_window rfacts extra (zone_word h))
    · exact .inr (.inl h)
  have live : names.trie.nodes.map (·.2)++[base]=(names.allocated base).trie.nodes.map (·.2) := by
    simp [Names.allocated]
  -- arena bytes outside the kept nodes are untouched
  have arenaKept : ∀ a, L.Arena a → ¬Kept (names.trie.nodes.map (·.2)++[base]) a →
      t.data.dmem.get? a=x.data.dmem.get? a := by
    intro a arena unkept
    apply frame a
    have heap : L.Heap a := by
      obtain ⟨span,member,within⟩ := arena
      exact ⟨span,List.mem_append_right _ member,within⟩
    rintro (h|h|h|h|h|h)
    · rw [stackT] at h
      exact rfacts.heap_window heap (zoneWindow a (zone_locals (by decide) h))
    · exact unkept ⟨down,List.mem_append_left _ (List.mem_map.mpr ⟨(downId,down),downNamed,rfl⟩),h⟩
    · exact unkept ⟨base,List.mem_append_right _ (List.mem_singleton_self _),h⟩
    · exact unkept (otherKept a h arena)
    · rw [stackT] at h
      exact rfacts.heap_window heap (zoneWindow a (zone_word h))
    · exact rfacts.heap_writes heap h
  obtain ⟨⟨d',device,same⟩,armedAfter,records,sites⟩ := facts.final inv
  obtain ⟨first,rest,streamEq,_,dropped,_⟩ := facts.one_record case
  have idle : A.Idle x.data.dmem ((names.allocated base).trie.nodes.map (·.2)) (stream.drop st.consumed) := by
    rw [←live,dropped]
    have before := compared.idle
    rw [streamEq] at before
    exact premises.allocator.frame _ _ _ _ before arenaKept
  have table : (names.allocated base).table=L.table := cut.table
  have peers : (names.allocated base).trie.peers=L.peers := cut.peers
  refine {
    pc := pc
    stack := rsp.trans stackT
    flight := compared.flight.later _ (by rw [rsp]; exact compared.flight.low)
      (by rw [rsp]; exact compared.flight.high) frame inside mapped flag calls.state
    calls := calls
    saved := ?_
    result := by rw [facts.result,answerZero]; exact zero_answer _ rbx
    inv := inv_of_relation table peers device (same.trans deviceEq) related shape armedAfter records sites
      cut.apart (fun node member => cut.named_arena (id:=node.1) member) idle
    seq := seq_kept cut.related.1 related cut.table table seqEq }
  intro a above
  rw [←compared.saved a above]
  symm
  apply frame a
  obtain ⟨j,bound,location⟩ := above
  have iw : insertWindow=200 := rfl
  have value : a.toNat=e.data.regs.rsp.toNat+48+j := by
    rw [location]
    have literal : (48 : BitVec 64).toNat=48 := rfl
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat,rspE,literal]
    omega
  have window : Window A s a := window_nat rfacts (by omega) (by omega)
  rintro (h|h|h|h|h|h)
  · rw [stackT] at h
    obtain ⟨i,inner,place⟩ := h
    rw [location] at place
    bv_omega
  · exact rfacts.heap_window (node_heap downArena h) window
  · exact rfacts.heap_window (node_heap cut.fresh h) window
  · exact rfacts.heap_window (otherHeap a h) window
  · rw [stackT] at h
    obtain ⟨i,inner,place⟩ := h
    rw [location] at place
    bv_omega
  · exact rfacts.writes_window h window

#print axioms cover_at_exit
end Binary.Statements.C1.Proof
