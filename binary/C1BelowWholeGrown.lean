import C1BelowAlloc
import C1BelowPrefixFinal

/-! Result C1, work package 3, the split path: the state after the second
allocation succeeded (`add+0x292`, the second object in `rax`), from
`Second.second_allocation`, `AllocResult`'s success clause and the open
hypothesis `NodeBelowTop`. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Statements.C1.Proof.Rollback
local instance : Labels := Image.linkedLabels

/-- Storing the word a location already holds changes no byte. -/
theorem store_read (m : DataMem) (address value : BitVec 64)
    (read : m.loadInt address 8 = some (value.toNat : Int)) (y : BitVec 64) :
    (m.storeInt address 8 value.toInt).get? y = m.get? y := by
  by_cases inside : InRange address 8 y
  · obtain ⟨i,bound,rfl⟩ := inside
    rw [MemoryBytes.get_of_loadInt _ _ _ _ (load64_store m address value) i bound,
      MemoryBytes.get_of_loadInt _ _ _ _ read i bound]
  · exact (storeInt_frame m address 8 _ y inside).symm

/-- The state at `add+0x292` after a successful second allocation, relative
to the state `a` at the comparison: the object and what `AllocResult`
promises of it, the bound of `NodeBelowTop`, the allocator idle with it
handed out, and every guarded byte as at `a`. -/
structure Grown (L : Layout) (A : Allocator) (c : Context) (s a t : MachineState) (live : List Nat)
    (rest : List HiddenRecord) (base2 : Nat) : Prop where
  pc : t.pc = Add.entry + 0x292
  stack : t.data.regs.rsp = a.data.regs.rsp
  rbx : t.data.regs.rbx = a.data.regs.rbx
  rbp : t.data.regs.rbp = a.data.regs.rbp
  r12 : t.data.regs.r12 = a.data.regs.r12
  r13 : t.data.regs.r13 = a.data.regs.r13
  r14 : t.data.regs.r14 = a.data.regs.r14
  r15 : t.data.regs.r15 = a.data.regs.r15
  object : t.data.regs.rax.toNat = base2
  nonzero : base2 ≠ 0
  aligned : base2 % 8 = 0
  arena : InArena L base2
  fresh : ∀ other ∈ live, disjointRanges base2 nodeSize other nodeSize = true
  zero : readNat t base2 nodeSize = .ok 0
  top : base2 + nodeSize < 2^64
  idle : A.Idle t.data.dmem (live ++ [base2]) rest
  flight : InFlight L A c s t
  calls : CallsReady c t.data
  kept : ∀ y, Guarded L s a live y → t.data.dmem.get? y = a.data.dmem.get? y
  mapped : MappedLe a.data.dmem t.data.dmem

theorem split_allocated (below : NodeBelowTop) (alloc : AllocRule) {fetch : Int64 → Option Decoded}
    {L : Layout} {A : Allocator} (premises : Premises fetch L A) {c : Context} {s a : MachineState}
    {family key cidr pid : Nat} {ra : UInt64} {live : List Nat}
    {record : HiddenRecord} {stream : List HiddenRecord} (bound : BitVec 8) (base : BitVec 64)
    (ready : insertReady L A c s family key cidr pid ra = .ok ())
    (apart : spansApart (objectsOf L) L.arena = true) (arena : ∀ node ∈ live, InArena L node)
    (pc : a.pc = Add.entry + 0x267)
    (flight : InFlight L A c s a)
    (high : a.data.regs.rsp.toNat + 48 ≤ s.data.regs.rsp.toNat)
    (low : s.data.regs.rsp.toNat + 48 ≤ a.data.regs.rsp.toNat + insertWindow)
    (calls : CallsReady c a.data)
    (boundRead : a.data.dmem.loadInt (a.data.regs.rsp.toBitVec+0x10) 1 = some bound.toNat)
    (baseRead : a.data.dmem.loadInt (a.data.regs.rsp.toBitVec+0x18) 8 = some base.toNat)
    (shorter : (a.data.regs.get (.low .r13 .W8)).toNat < bound.toNat)
    (site : record.site = 79) (success : record.bytes.head? = some 1)
    (idle : A.Idle a.data.dmem live (record :: stream)) :
    Eventually (instructionStep fetch) (fun t => ∃ base2, Grown L A c s a t live stream base2) a := by
  have facts := ready_facts ready
  have window := window_bounds facts
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (eventually_flight (Second.second_allocation alloc fetch L A premises c s a family key cidr pid ra live
      record stream bound base ready apart arena pc flight high low calls boundRead baseRead shorter site idle))
  rintro t ⟨⟨pcT,stack,rbx,rbp,r12,r13,r14,r15,result,flightT,callsT,covered,frameC,kept⟩,mapped,_⟩
  obtain ⟨nonzero,aligned,inArena,fresh,zero,idleT⟩ := result.2 success
  have top := below fetch L A premises live record stream t result success
  refine ⟨t.data.regs.rax.toNat,pcT,stack,rbx,rbp,r12,r13,r14,r15,rfl,nonzero,aligned,inArena,fresh,zero,top,
    idleT,flightT,callsT,?_,mapped⟩
  intro y guarded
  have pushWindow {x : BitVec 64} (inside : InRange (a.data.regs.rsp.toBitVec-8) 8 x) : Window A s x :=
    scratch_window (words_scratch facts high low (words_push inside))
  have notPush : ¬InRange (a.data.regs.rsp.toBitVec - 8) 8 y := by
    rcases guarded with stack | ⟨span,fixed,inside⟩ | keptNode | cache
    · exact above_push (by omega) (by omega) stack
    · exact fun push => facts.heap_window ⟨span,List.mem_append_left _ fixed,inside⟩ (pushWindow push)
    · exact fun push => facts.heap_window (Rollback.arena_heap (kept_arena arena keptNode)) (pushWindow push)
    · exact fun push => facts.scratch_cache (words_scratch facts high low (words_push push)) cache
  have notWritten : ¬c.writes y := by
    rcases guarded with stack | ⟨span,fixed,inside⟩ | keptNode | cache
    · intro written
      apply facts.writes_window written
      obtain ⟨i,small,location⟩ := stack
      have rsp : a.data.regs.rsp.toBitVec.toNat = a.data.regs.rsp.toNat := rfl
      have position : y.toNat = a.data.regs.rsp.toNat + i := by
        rw [location,BitVec.toNat_add,BitVec.toNat_ofNat,rsp]
        omega
      unfold insertWindow at low window
      apply window_nat facts
      · unfold insertWindow; omega
      · omega
    · exact facts.heap_writes ⟨span,List.mem_append_left _ fixed,inside⟩
    · exact facts.heap_writes (Rollback.arena_heap (kept_arena arena keptNode))
    · exact fun written => facts.writes_cache written cache
  rw [kept y guarded,←frameC y (fun h => h.elim notPush notWritten)]
  exact store_read _ _ _ baseRead y

#print axioms split_allocated
end Binary.Statements.C1.Proof
