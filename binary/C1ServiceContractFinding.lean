import C1ServiceRules
import C1ServiceHistory
import StackFrame

/-! Result C1, work package 4: a STATEMENT FINDING on `AllocatorContract`, with
its evidence. Nothing here is used by the acceptance theorems.

The contract's two service clauses quantify over every coverage context `c`
that is valid at the service's entry (`ServiceReady.coverage : c.At …`) and
promise `c.At` again at the return. `ServiceReady` says nothing about WHERE
that context's bytes are: the task's coverage fields (found through the
current-task word), the buffer and the preemption count may lie anywhere,
including in the arena and in the service's stack scratch. A conforming
service must therefore leave every such context valid, which forbids it to
change any four bytes that some context reads as its mode word. An allocator
has to change its own state in the arena on a successful allocation.

`word_kept`: take any admissible entry state of the allocation service and
any four bytes `word` (apart from the two per-CPU words, holding a value that
is not a recording mode). Move the current-task word so that the task's mode
field is `word`, and clear the preemption count. The state is still
admissible (the per-CPU words are outside the arena, so `Idle` is unaffected,
by the contract's own `frame` clause), and from it a conforming service
returns WITH `word` UNCHANGED. So a service that advances a state word at a
fixed arena address on every successful allocation, from every state (the
packet's test model does: `+16`, the index of the next answer), does not meet
the contract.

`no_state_word`: in particular no allocator whose `Idle` pins a four-byte
arena word to a value that a successful allocation changes meets the
contract, as soon as it is idle in one admissible entry state.

Consequence: no allocator that keeps mutable state in ordinarily mapped
memory meets the contract as signed. It CAN be met, by a service whose one
mutable byte has unmapped neighbours, so that no read of two or more bytes
contains it: `C1ServiceStub`, `Stub.contract`. That stub is what
`PremisesMet` is closed with. It is evidence that the signed text is
satisfiable, and that what it admits is not an allocator.

The smallest repair is to let `ServiceReady` say what the caller's conditions
already give (`Separated` below): the service's stack, the arena and the
coverage bytes are pairwise apart, and the buffer is apart from the coverage
metadata. `separated` derives exactly that from `insertReady` and `InFlight`,
so `AllocRule` and `FreeRule` stay derivable under the repaired contract. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-! ## The aliased state -/

/-- The two per-CPU words every coverage context reads: the current-task
pointer and the preemption count. -/
def PerCpu (a : BitVec 64) : Prop :=
  InRange currentTaskAddress 8 a ∨ InRange preemptCountAddress 4 a

/-- Memory `m` with the current task moved so that its mode field (`task+0x6e0`)
is the word at `word`, and the preemption count cleared. -/
def aliased (m : Mem 64) (word : BitVec 64) : Mem 64 :=
  (m.storeInt currentTaskAddress 8 (word - 0x6e0).toInt).storeInt preemptCountAddress 4 (0#32).toInt

theorem aliased_frame (m : Mem 64) (word : BitVec 64) : EqualOutside PerCpu m (aliased m word) :=
  (storeInt_frame m currentTaskAddress 8 _).trans (storeInt_frame _ preemptCountAddress 4 _)

private theorem words_apart (a : BitVec 64) (inside : InRange currentTaskAddress 8 a) :
    ¬InRange preemptCountAddress 4 a :=
  InRange.offset_disjoint currentTaskAddress 0 8 8 4 (by decide) (by decide) (by decide) a
    (by simpa using inside)

theorem aliased_task (m : Mem 64) (word : BitVec 64) :
    load64 (aliased m word) currentTaskAddress = some (word - 0x6e0) := by
  have kept := (storeInt_frame (m.storeInt currentTaskAddress 8 (word - 0x6e0).toInt)
    preemptCountAddress 4 (0#32).toInt).loadInt currentTaskAddress 8
    (fun i bound => words_apart _ ⟨i,bound,rfl⟩)
  unfold load64 aliased
  rw [← kept, load64_store]
  simp only [Option.map_some, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem aliased_preempt (m : Mem 64) (word : BitVec 64) :
    load32 (aliased m word) preemptCountAddress = some 0 := by
  unfold load32 aliased
  rw [load32_store]
  simp only [Option.map_some, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

theorem aliased_mapped (m : Mem 64) (word a : BitVec 64) (mapped : (m.get? a).isSome = true) :
    ((aliased m word).get? a).isSome = true := by
  have one := (loadInt_defined m a 1).mpr (fun k small => by
    have zero : k = 0 := by omega
    subst zero
    simpa using mapped)
  have after : ((aliased m word).loadInt a 1).isSome = true :=
    storeInt_defined _ _ preemptCountAddress 1 4 (0#32).toInt
      (storeInt_defined m _ currentTaskAddress 1 8 (word - 0x6e0).toInt one)
  generalize aliased m word = memory at after ⊢
  simpa using (loadInt_defined _ _ 1).mp after 0 (by omega)

/-! ## The finding -/

/-- THE WORD IS KEPT. From any admissible entry state of the allocation
service, and any four bytes `word` apart from the two per-CPU words whose
value `v` is not a recording mode: the state `moved`, which differs from `s`
only in the two per-CPU words, is admissible for a context that reads `word`
as its mode, and a conforming service returns from it with `word` still `v`. -/
theorem word_kept {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator}
    (contract : AllocatorContract fetch L A)
    {word : BitVec 64} {v : BitVec 32}
    (wordApart : ∀ a, InRange word 4 a → ¬PerCpu a)
    (arenaApart : ∀ a, L.Arena a → ¬PerCpu a)
    {c : Context} {s : MachineState} {ra : UInt64} {live : List Nat} {record : HiddenRecord}
    {stream : List HiddenRecord}
    (entry : s.pc = allocEntry) (frame : EntryFrame s ra) (ready : ServiceReady A c s)
    (stackApart : ∀ a, InRange s.data.regs.rsp.toBitVec 8 a → ¬PerCpu a)
    (cache : s.data.regs.rdi.toNat = L.cache) (flags : s.data.regs.get (.low .rsi .W32) = 0xdc0#32)
    (site : (ra.toNat, record.site) ∈ allocSites)
    (idle : A.Idle s.data.dmem live (record :: stream))
    (value : load32 s.data.dmem word = some v) (quiet : v ≠ 2 ∧ v ≠ 3) :
    ∃ (memory : Mem 64) (context : Context) (t : MachineState),
      let moved : MachineState := ⟨{s.data with dmem := memory},s.pc⟩
      EqualOutside PerCpu s.data.dmem memory ∧
      EntryFrame moved ra ∧ ServiceReady A context moved ∧
      A.Idle memory live (record :: stream) ∧
      Returned moved t ra ∧ AllocResult L A live record stream t ∧
      load32 t.data.dmem word = some v := by
  have same := aliased_frame s.data.dmem word
  have task := aliased_task s.data.dmem word
  have count := aliased_preempt s.data.dmem word
  have mapped := aliased_mapped s.data.dmem word
  generalize aliased s.data.dmem word = memory at same task count mapped
  have idleMoved : A.Idle memory live (record :: stream) :=
    contract.frame _ _ _ _ idle (fun a arena _ => same a (arenaApart a arena))
  have wordRead : load32 memory word = some v := by
    rw [← value]
    unfold load32
    rw [same.loadInt word 4 (fun i bound => wordApart _ ⟨i,bound,rfl⟩)]
  have field : word - 0x6e0 + 0x6e0 = word := BitVec.sub_add_cancel word 0x6e0
  have modeRead (coverage : KcovLayout) : LookupModeRead coverage 0 := by
    simp [LookupModeRead]
  have softRead : ¬LookupSoftRead 0 := by
    simp [LookupSoftRead]
  have notNeeded : ¬(Context.mk ⟨word - 0x6e0,0,0,v,0⟩ 0).Needed := by
    rintro ⟨-,mode | mode⟩
    · exact quiet.1 mode
    · exact quiet.2 mode
  have at_ : Context.At ⟨⟨word - 0x6e0,0,0,v,0⟩,0⟩ memory := by
    refine ⟨⟨task,fun read => (softRead read).elim,fun _ => ?_,fun needed => (notNeeded needed).elim⟩,count⟩
    show load32 memory (word - 0x6e0 + 0x6e0) = _
    rw [field]
    exact wordRead
  have readyMoved : ServiceReady A ⟨⟨word - 0x6e0,0,0,v,0⟩,0⟩ ⟨{s.data with dmem := memory},s.pc⟩ :=
    ⟨at_,fun needed => (notNeeded needed).elim,ready.forward,
      fun i bound => mapped _ (ready.stackMapped i bound)⟩
  have frameMoved : EntryFrame ⟨{s.data with dmem := memory},s.pc⟩ ra := by
    refine ⟨frame.1,?_⟩
    show memory.loadInt s.data.regs.rsp.toBitVec 8 = _
    rw [← same.loadInt _ 8 (fun i bound => stackApart _ ⟨i,bound,rfl⟩)]
    exact frame.2
  obtain ⟨t,returned,-,coverage,result⟩ := eventually_ends
    (contract.alloc _ ⟨{s.data with dmem := memory},s.pc⟩ ra live record stream entry frameMoved
      readyMoved cache flags site idleMoved)
  have mode : load32 t.data.dmem (word - 0x6e0 + 0x6e0) = some v := coverage.1.2.2.1 (modeRead _)
  rw [field] at mode
  exact ⟨memory,_,t,same,frameMoved,readyMoved,idleMoved,returned,result,mode⟩

/-- NO ALLOCATOR WITH A STATE WORD MEETS THE CONTRACT. Let `Idle` pin the four
bytes at `word` to `code live stream`, a value that a successful allocation
changes; let the arena and the word avoid the two per-CPU words. Then no
admissible entry state with a pending success (whose pinned value is not a
recording mode, 2 or 3) exists: from one, the contract is refuted. -/
theorem no_state_word {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator}
    (contract : AllocatorContract fetch L A)
    {word : BitVec 64} {code : List Nat → List HiddenRecord → BitVec 32}
    (pinned : ∀ m live stream, A.Idle m live stream → load32 m word = some (code live stream))
    (moves : ∀ live record stream object, code (live ++ [object]) stream ≠ code live (record :: stream))
    (wordApart : ∀ a, InRange word 4 a → ¬PerCpu a)
    (arenaApart : ∀ a, L.Arena a → ¬PerCpu a)
    {c : Context} {s : MachineState} {ra : UInt64} {live : List Nat} {record : HiddenRecord}
    {stream : List HiddenRecord}
    (entry : s.pc = allocEntry) (frame : EntryFrame s ra) (ready : ServiceReady A c s)
    (stackApart : ∀ a, InRange s.data.regs.rsp.toBitVec 8 a → ¬PerCpu a)
    (cache : s.data.regs.rdi.toNat = L.cache) (flags : s.data.regs.get (.low .rsi .W32) = 0xdc0#32)
    (site : (ra.toNat, record.site) ∈ allocSites)
    (idle : A.Idle s.data.dmem live (record :: stream))
    (quiet : code live (record :: stream) ≠ 2 ∧ code live (record :: stream) ≠ 3)
    (success : record.bytes.head? = some 1) : False := by
  obtain ⟨memory,context,t,-,-,-,-,-,result,kept⟩ := word_kept contract wordApart arenaApart entry frame
    ready stackApart cache flags site idle (pinned _ _ _ idle) quiet
  have after := pinned _ _ _ (result.2 success).2.2.2.2.2
  exact moves live record stream _ (Option.some.inj (after.symm.trans kept))

#print axioms word_kept
#print axioms no_state_word

/-! ## The repair: what the caller's conditions already give -/

/-- What `ServiceReady` would have to add: the service's stack (its scratch
and its return word), the arena and the coverage bytes are pairwise apart,
and the coverage buffer is apart from the coverage metadata and the
preemption count. -/
structure Separated (L : Layout) (A : Allocator) (c : Context) (e : MachineState) : Prop where
  stackArena : ∀ a, Scratch e A.depth a ∨ InRange e.data.regs.rsp.toBitVec 8 a → ¬L.Arena a
  stackCoverage : ∀ a, Scratch e A.depth a ∨ InRange e.data.regs.rsp.toBitVec 8 a → ¬c.bytes a
  coverageArena : ∀ a, c.bytes a → ¬L.Arena a
  bufferMetadata : ∀ a, c.writes a → ¬c.metadataBytes a ∧ ¬InRange preemptCountAddress 4 a

/-- The repaired readiness holds at every service entry inside an insertion:
the two rules stay derivable. -/
theorem separated {L : Layout} {A : Allocator} {c : Context} {s e : MachineState}
    {family key cidr pid : Nat} {ra : UInt64}
    (callReady : insertReady L A c s family key cidr pid ra = .ok ())
    (flight : InFlight L A c s e) : Separated L A c e := by
  have ready := ready_of_insertReady callReady
  have g := ready.geometry flight.low flight.high
  have stack (a : BitVec 64)
      (inside : Scratch e A.depth a ∨ InRange e.data.regs.rsp.toBitVec 8 a) :
      (stackSpan A s).contains a := stack_of_service g inside
  have coverage (a : BitVec 64) (read : c.bytes a) : ∃ span ∈ Trie.callServices c, span.contains a := by
    obtain ⟨span,member,contains⟩ := Trie.readSpans_cover read
    exact ⟨span,by simp [Trie.callServices, member],contains⟩
  refine ⟨?_,?_,?_,?_⟩
  · rintro a inside ⟨span,member,contains⟩
    exact spansApart_sound ready.heapStack (show span ∈ L.heap by simp [Layout.heap, member])
      (by simp) contains (stack a inside)
  · intro a inside read
    obtain ⟨span,member,contains⟩ := coverage a read
    exact spansApart_sound ready.servicesStack member (by simp) contains (stack a inside)
  · rintro a read ⟨span,member,contains⟩
    obtain ⟨service,serviceMember,serviceContains⟩ := coverage a read
    exact spansApart_sound ready.heapServices (show span ∈ L.heap by simp [Layout.heap, member])
      serviceMember contains serviceContains
  · intro a write
    obtain ⟨buffer,member,contains⟩ := Trie.writeSpans_cover write
    have bufferMember : buffer ∈ Trie.callBuffers c := by simp [Trie.callBuffers, member]
    constructor
    · intro metadata
      obtain ⟨span,spanMember,spanContains⟩ := Trie.metadataSpans_cover metadata
      exact spansApart_sound ready.buffersMetadata bufferMember
        (show span ∈ Trie.callMetadata c ++ [(preemptCountAddress.toNat,4)] by
          simp [Trie.callMetadata, spanMember]) contains spanContains
    · intro count
      exact spansApart_sound ready.buffersMetadata bufferMember
        (show (preemptCountAddress.toNat,4) ∈ Trie.callMetadata c ++ [(preemptCountAddress.toNat,4)] by
          simp) contains
        (by simpa only [Pair.Span.contains, BitVec.ofNat_toNat, BitVec.setWidth_eq] using count)

#print axioms separated
end Binary.Statements.C1.Proof
