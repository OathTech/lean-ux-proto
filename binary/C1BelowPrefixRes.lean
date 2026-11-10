import C1BelowPrefixCut
import C1BelowFlight

/-! Result C1, work package 3, prefix: the separations the machine lemmas take
(`Res`), derived from `NodeCut`, `CutExtra` and the caller's conditions. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

variable {L : Layout} {A : Allocator} {c : Context} {s : MachineState} {family : Nat} {ra : UInt64}

/-- The window does not wrap: the caller's conditions check its span against
the (nonempty) heap. -/
theorem ReadyFacts.window_bounds (facts : ReadyFacts L A c s family ra) :
    insertWindow+A.depth≤s.data.regs.rsp.toNat ∧ s.data.regs.rsp.toNat+8≤2^64 := by
  have member : (L.table+AllowedipsMutationLayout.root4,8) ∈ L.heap := by
    apply List.mem_append_left
    apply List.mem_append_left
    simp [tableFields]
  have checked := List.all_eq_true.mp (List.all_eq_true.mp facts.heapApart _ member) (ownWindow A s)
    (List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))
  have parts : (ownWindow A s).1+(ownWindow A s).2≤2^64 := by
    simp only [Bool.and_eq_true,decide_eq_true_eq] at checked
    exact checked.1.2
  simp only [ownWindow,BitVec.toNat_sub,BitVec.toNat_ofNat] at parts
  have rsp : s.data.regs.rsp.toBitVec.toNat=s.data.regs.rsp.toNat := rfl
  have small := s.data.regs.rsp.toBitVec.isLt
  rw [rsp] at parts small
  omega

theorem window_nat (facts : ReadyFacts L A c s family ra) {a : BitVec 64}
    (low : s.data.regs.rsp.toNat≤a.toNat+(insertWindow+A.depth))
    (high : a.toNat<s.data.regs.rsp.toNat+8) : Window A s a := by
  obtain ⟨fits,top⟩ := facts.window_bounds
  refine ⟨a.toNat+(insertWindow+A.depth)-s.data.regs.rsp.toNat,by omega,?_⟩
  have rsp : s.data.regs.rsp.toBitVec.toNat=s.data.regs.rsp.toNat := rfl
  bv_omega

theorem zone_nat {stack : UInt64} {a : BitVec 64} (low : 48≤stack.toNat) (high : stack.toNat+48≤2^64)
    (zone : Zone stack a) : stack.toNat≤a.toNat+48 ∧ a.toNat<stack.toNat+48 := by
  obtain ⟨i,bound,location⟩ := zone
  have rsp : stack.toBitVec.toNat=stack.toNat := rfl
  constructor <;> bv_omega

theorem arena_heap {address offset size : Nat} (arena : InArena L address) (within : offset+size≤72)
    {a : BitVec 64} (inside : InRange (.ofNat 64 (address+offset)) size a) : L.Heap a := by
  obtain ⟨span,member,low,high⟩ := arena
  obtain ⟨i,bound,location⟩ := inside
  unfold nodeSize at high
  refine ⟨span,List.mem_append_right _ member,address-span.1+offset+i,by omega,?_⟩
  rw [location]
  bv_omega

theorem fixed_peer {id address offset size : Nat} (named : (id,address) ∈ L.peers)
    (field : (offset,size) ∈ peerFields Root.nodeOffsets)
    {a : BitVec 64} (inside : InRange (.ofNat 64 (address+offset)) size a) : L.Heap a :=
  ⟨(address+offset,size),List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨(id,address),named,List.mem_map.mpr ⟨(offset,size),field,rfl⟩⟩)),inside⟩

theorem fixed_table {offset size : Nat} (field : (offset,size) ∈ tableFields)
    {a : BitVec 64} (inside : InRange (.ofNat 64 (L.table+offset)) size a) : L.Heap a :=
  ⟨(L.table+offset,size),List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨(offset,size),field,rfl⟩)),inside⟩

section
variable {fetch : Int64 → Option Decoded} {w : World} {d : Device} {key cidr pid : Nat}
  {stream : List HiddenRecord} {placed : Option NodeId} {names : Allowedips.Names} {base : Nat}
  {e : MachineState}

theorem NodeCut.named_arena (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e)
    {id address : Nat} (named : (id,address) ∈ (names.allocated base).trie.nodes) : InArena L address := by
  rcases List.mem_append.mp named with old|new
  · exact cut.arena _ old
  · cases List.mem_singleton.mp new
    exact cut.fresh

/-- Everything reconstruction reads under the extended names is heap. -/
theorem NodeCut.read_heap (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e) :
    ∀ span ∈ readSpans (names.allocated base) Root.nodeOffsets, ∀ a, span.contains a → L.Heap a := by
  intro span member a inside
  rcases List.mem_append.mp member with table|rest
  · obtain ⟨⟨offset,size⟩,field,rfl⟩ := List.mem_map.mp table
    have same : (names.allocated base).table=L.table := cut.table
    rw [same] at inside
    exact fixed_table field inside
  · rcases List.mem_append.mp rest with node|peer
    · obtain ⟨⟨id,address⟩,named,mapped⟩ := List.mem_flatMap.mp node
      obtain ⟨⟨offset,size⟩,field,rfl⟩ := List.mem_map.mp mapped
      have all : ∀ f ∈ nodeFields Root.nodeOffsets, f.1+f.2≤72 := by decide
      exact arena_heap (cut.named_arena named) (all _ field) inside
    · obtain ⟨⟨id,address⟩,named,mapped⟩ := List.mem_flatMap.mp peer
      obtain ⟨⟨offset,size⟩,field,rfl⟩ := List.mem_map.mp mapped
      have same : (names.allocated base).trie.peers=L.peers := cut.peers
      rw [same] at named
      exact fixed_peer named field inside

/-- The heap bytes the first initialization writes are heap. -/
theorem NodeCut.init_heap (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e)
    {a : BitVec 64} (written : InRange (.ofNat 64 base) 72 a ∨ ListWrites (names.allocated base) a) :
    L.Heap a := by
  rcases written with fresh|⟨link,slot,offset,which,inside⟩
  · exact arena_heap (offset:=0) cut.fresh (by decide) fresh
  · cases slot with
    | node named =>
      rw [Nat.add_assoc] at inside
      exact arena_heap (cut.named_arena named) (by rcases which with rfl|rfl <;> decide) inside
    | peer named =>
      have same : (names.allocated base).trie.peers=L.peers := cut.peers
      rw [same] at named
      rw [Nat.add_assoc] at inside
      exact fixed_peer named (by rcases which with rfl|rfl <;> decide) inside

/-- `Res` from the cut, the extra facts and the caller's conditions. -/
theorem resources (facts : ReadyFacts L A c s family ra)
    (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e)
    (extra : CutExtra L s e family) : Res names c e.data base := by
  obtain ⟨fits,top⟩ := facts.window_bounds
  have high := extra.frameHigh
  have low := extra.frameLow
  unfold insertWindow at fits low
  have rspE : e.data.regs.rsp.toBitVec.toNat=e.data.regs.rsp.toNat := rfl
  have rspS : s.data.regs.rsp.toBitVec.toNat=s.data.regs.rsp.toNat := rfl
  have zoneWindow : ∀ a, Zone e.data.regs.rsp a → Window A s a := by
    intro a zone
    obtain ⟨lo,hi⟩ := zone_nat (by omega) (by omega) zone
    exact window_nat facts (by unfold insertWindow; omega) (by omega)
  refine {
    mapped := ?_
    extent := by omega
    context := fun a read zone => facts.bytes_window read (zoneWindow a zone)
    contextInit := ?_
    heapZone := fun a written zone => facts.heap_window (cut.init_heap written) (zoneWindow a zone)
    projection := ?_
    table := ?_
    query := ?_ }
  · apply cut.flight.mapped
    rw [loadInt_defined]
    intro i bound
    have byte := facts.stackMapped (s.data.regs.rsp.toNat-e.data.regs.rsp.toNat+47-i)
      (by unfold insertWindow; omega)
    have address : e.data.regs.rsp.toBitVec-48+BitVec.ofNat 64 i=
        s.data.regs.rsp.toBitVec-BitVec.ofNat 64 (s.data.regs.rsp.toNat-e.data.regs.rsp.toNat+47-i+1) := by
      bv_omega
    rw [address]
    exact byte
  · rintro a read (fresh|list|⟨offset,member,inside⟩)
    · exact facts.heap_bytes (cut.init_heap (.inl fresh)) read
    · exact facts.heap_bytes (cut.init_heap (.inr list)) read
    · rw [BitVec.ofNat_add,Root.ofNat_uint64] at inside
      have small : offset+1≤48 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        omega
      exact facts.bytes_window read (zoneWindow a (zone_local small inside))
  · intro span member a inside
    have heap := cut.read_heap span member a inside
    rintro (zone|written)
    · exact facts.heap_window heap (zoneWindow a zone)
    · exact facts.heap_writes heap written
  · rintro a ⟨i,bound,location⟩
    rw [cut.table] at location
    have heap : L.Heap a := by
      by_cases first : i<8
      · exact fixed_table (offset:=0) (size:=8) (by decide) ⟨i,first,location⟩
      · by_cases second : i<16
        · refine fixed_table (offset:=8) (size:=8) (by decide) ⟨i-8,by omega,?_⟩
          rw [location]
          bv_omega
        · refine fixed_table (offset:=16) (size:=8) (by decide) ⟨i-16,by omega,?_⟩
          rw [location]
          bv_omega
    rintro (zone|written)
    · exact facts.heap_window heap (zoneWindow a zone)
    · exact facts.heap_writes heap written
  · rintro a ⟨i,bound,location⟩
    have keyLow := extra.keyLow
    have keyHigh := extra.keyHigh
    have r13 : e.data.regs.r13.toBitVec.toNat=e.data.regs.r13.toNat := rfl
    have position : a.toNat=e.data.regs.r13.toNat+i := by
      rw [location]
      bv_omega
    rintro (zone|written)
    · obtain ⟨lo,hi⟩ := zone_nat (by omega) (by omega) zone
      omega
    · exact facts.writes_window written (window_nat facts (by unfold insertWindow; omega) (by omega))

#print axioms resources
end
end Binary.Statements.C1.Proof
