import C1WitnessStub
import PairServiceCall
import MemoryBytes

/-! Result C1, open proposition `WitnessHolds`: the active stub meets
`AllocatorContract` as signed (`contract`), and from an entry state whose
coverage buffer is in use with room for a record it returns having changed a
byte of its scratch and a byte of the buffer (`alloc_active`).

The run is: `push %rdi`; the actual `call` of `__sanitizer_cov_trace_pc`,
whose behaviour is the landed contract `TracePcContract`; `pop %rdi`; then
package 4's body. The allocator's bytes are in the arena, apart from the
scratch and from the coverage bytes by `ServiceReady.separated`, so package
4's `Idle` crosses the three new instructions by its own frame clause. -/
namespace Binary.Statements.C1.Witness
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.Statements.C1.Proof
open Binary.Statements.C1.Stub Binary.Instrumentation
local instance : Labels := Image.linkedLabels

variable {fetch : Int64 → Option Decoded}

local macro "stub_instr" agree:ident : tactic => `(tactic|
  (apply step_instr ($agree _ _ (by rfl)) (by decide)
   simp only [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
     MachineData.load, MachineData.store, MachineData.set, MachineData.setReg,
     AddrExpr.interp, ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set,
     Reg64s.set64, Reg.base, Reg.offset, BitVec.drop, BitVec.take,
     BitVec.toAddressSize, Effects.All]))

local macro "stub_load" read:ident : tactic => `(tactic|
  (simp [BitVec.signed]
   rw [$read:ident]
   simp only [Effects.All]))

/-! ## The callback, with its exact effect kept -/

def target : Label := "L_ffffffff810f31f0"

theorem return_read {s : MachineState} {ra : UInt64} (entry : EntryFrame s ra) :
    load64 s.data.dmem s.data.regs.rsp.toBitVec = some ra.toBitVec := by
  simp only [load64, entry.2, Option.map_some, BitVec.ofInt_natCast]
  apply congrArg some
  apply BitVec.eq_of_toNat_eq
  simp

/-- The actual `call` of the PC callback and its landed contract: the state
after it, the coverage state, the frame, and the callback's exact stores. -/
theorem traced (tracePc : TracePcContract fetch) (pc : Int64)
    (here : fetch pc = some ⟨callInstruction target,5⟩)
    (c : Context) (s : MachineData) (ready : CallsReady c s) :
    Eventually (instructionStep fetch) (fun t =>
      Returned (calledState s (pc+5) (label target)) t (pc+5).toUInt64 ∧
      c.At t.data.dmem ∧
      EqualOutside c.writes (calledState s (pc+5) (label target)).data.dmem t.data.dmem ∧
      KcovEffect .pc (calledState s (pc+5) (label target)) t) ⟨s,pc⟩ := by
  have first : Eventually (instructionStep fetch) (fun t => t = calledState s (pc+5) (label target))
      ⟨s,pc⟩ :=
    Sequential.forget (s := ⟨⟨s,pc⟩,[]⟩)
      (historySteps_eventually fetch _ _ _ (call_instruction fetch pc target here s [] ready.mapped))
      (fun t h => h.1)
  apply eventually_trans (instructionStep fetch) _ _ _ first
  rintro entered rfl
  have entry := called_ready c s (pc+5) (label target) ready
  have returnRead := return_read entry.1
  have run := tracePc (calledState s (pc+5) (label target)) (pc+5).toUInt64 rfl
    (CommonBitsCoverage.ready c .pc _ _ entry.2 returnRead
      (by simpa [calledState] using ready.returnSeparate)) entry.1
  apply Sequential.forget run
  rintro t ⟨returned,frame,effect,-⟩
  have preserved := state_preserved c .pc _ t.machine _ entry.2 returnRead
    ready.metadataSeparate ready.preemptSeparate effect frame
  exact ⟨returned,preserved.1,preserved.2,effect⟩

/-! ## The three new instructions -/

/-- The state after `push %rdi`. -/
def pushed (d : MachineData) : MachineData :=
  {d with regs := {d.regs with rsp := d.regs.rsp - 8}, dmem := d.dmem.storeInt (d.regs.rsp.toBitVec - 8) 8 d.regs.rdi.toBitVec.toInt}

/-- The callback's entry state inside the stub. -/
def entered (d : MachineData) : MachineState :=
  calledState (pushed d) (allocEntry+1+5) (label target)

/-- `push %rdi`, the callback, `pop %rdi`: the stub reaches its body with `rdi`
and the stack pointer restored, the callee-saved registers kept, and memory
the callback's memory. -/
theorem front (agree : ∀ pc i, Witness.fetch pc = some i → fetch pc = some i)
    (tracePc : TracePcContract fetch) (c : Context) (d : MachineData)
    (mapped : (d.dmem.loadInt (d.regs.rsp.toBitVec - 8) 8).isSome = true)
    (ready : CallsReady c (pushed d))
    (savedApart : ∀ a, c.writes a → ¬InRange (d.regs.rsp.toBitVec - 8) 8 a)
    (P : MachineState → Prop)
    (finish : ∀ (u : MachineData) (t : MachineState),
      u.regs.rsp = d.regs.rsp → u.regs.rdi = d.regs.rdi →
      u.regs.rbx = d.regs.rbx → u.regs.rbp = d.regs.rbp → u.regs.r12 = d.regs.r12 →
      u.regs.r13 = d.regs.r13 → u.regs.r14 = d.regs.r14 → u.regs.r15 = d.regs.r15 →
      u.dmem = t.data.dmem → c.At u.dmem →
      u.dmem.loadInt (d.regs.rsp.toBitVec - 8) 8 = some (d.regs.rdi.toNat : Int) →
      EqualOutside c.writes (entered d).data.dmem u.dmem →
      KcovEffect .pc (entered d) t →
      Eventually (instructionStep fetch) P ⟨u,allocEntry+7⟩) :
    Eventually (instructionStep fetch) P ⟨d,allocEntry⟩ := by
  obtain ⟨word,loaded⟩ := Option.isSome_iff_exists.mp mapped
  stub_instr agree
  simp [Width.bytesv]
  rw [show d.dmem.loadInt (d.regs.rsp.toBitVec - 8#64) 8 = some word from loaded]
  simp only [Effects.All]
  show Eventually (instructionStep fetch) P ⟨pushed d,allocEntry+1⟩
  have here : fetch (allocEntry+1) = some ⟨callInstruction target,5⟩ := agree _ _ (by rfl)
  apply eventually_trans (instructionStep fetch) _ _ _ (traced tracePc (allocEntry+1) here c (pushed d) ready)
  rintro ⟨td,tpc⟩ ⟨returned,state,frame,effect⟩
  obtain ⟨pcT,sp,bx,bp,r12,r13,r14,r15⟩ := returned_caller (pushed d) _ _ _ returned
  change tpc = _ at pcT
  subst pcT
  have savedRead : td.dmem.loadInt (d.regs.rsp.toBitVec - 8) 8 = some (d.regs.rdi.toNat : Int) := by
    rw [← frame.loadInt (d.regs.rsp.toBitVec - 8) 8 (fun i bound written =>
      savedApart _ written ⟨i,bound,rfl⟩)]
    show ((pushed d).dmem.storeInt ((d.regs.rsp.toBitVec - 8) - 8) 8 _).loadInt _ 8 = _
    rw [← (storeInt_frame (pushed d).dmem _ 8 _).loadInt (d.regs.rsp.toBitVec - 8) 8 (fun i bound => by
      have base : d.regs.rsp.toBitVec - 8 - 8 = (d.regs.rsp.toBitVec - 16) + .ofNat 64 0 := by bv_omega
      have next : d.regs.rsp.toBitVec - 8 = (d.regs.rsp.toBitVec - 16) + .ofNat 64 8 := by bv_omega
      rw [base, next]
      exact fun inside => InRange.offset_disjoint (d.regs.rsp.toBitVec - 16) 8 8 0 8 (by omega) (by omega)
        (.inr (by omega)) _ ⟨i,bound,rfl⟩ inside)]
    exact load64_store d.dmem _ d.regs.rdi.toBitVec
  have popRead : td.dmem.loadInt td.regs.rsp.toBitVec 8 = some (d.regs.rdi.toNat : Int) := by
    rw [show td.regs.rsp = d.regs.rsp - 8 from sp]
    exact savedRead
  stub_instr agree
  stub_load popRead
  rw [show allocEntry + 1 + 5 + 1 = allocEntry + 7 by decide +kernel]
  refine finish _ ⟨td,allocEntry+1+5⟩ ?_ ?_ bx bp r12 r13 r14 r15 rfl state savedRead frame effect
  · show td.regs.rsp + 8 = d.regs.rsp
    rw [show td.regs.rsp = d.regs.rsp - 8 from sp]
    apply UInt64.toBitVec_inj.mp
    exact BitVec.sub_add_cancel _ _
  · apply UInt64.toBitVec_inj.mp
    simp

/-! ## Package 4's body, seven bytes further on -/

/-- The six instructions both paths share, up to the branch. -/
local macro "stub_prefix" agree:ident cache:ident stateRead:ident tableRead:ident : tactic => `(tactic|
  (stub_instr $agree
   simp [$cache:ident, state, BitVec.signed]
   rw [$stateRead:ident]
   simp only [Effects.All]
   stub_instr $agree
   simp [BitVec.signed]
   stub_instr $agree
   stub_load $stateRead
   stub_instr $agree
   stub_load $tableRead
   stub_instr $agree
   simp [BitVec.signed]
   stub_instr $agree
   simp))

/-- The body, executed (package 4's `alloc_run` at its new address): with
`count` answers given and the pending outcome byte `code`, it stores `count+1`
in the state byte and returns object `count` (outcome 1) or NULL (outcome 0),
changing nothing else in memory. -/
theorem body_run (agree : ∀ pc i, Witness.fetch pc = some i → fetch pc = some i)
    (d : MachineData) (ra : UInt64) (count : Nat) (small : count < slots) (code : Int)
    (binary : code = 0 ∨ code = 1)
    (cache : d.regs.rdi = UInt64.ofNat state)
    (stateRead : d.dmem.loadInt (.ofNat 64 state) 1 = some (count : Int))
    (tableRead : (d.dmem.storeInt (.ofNat 64 state) 1 ((count : Int)+1)).loadInt
      (.ofNat 64 (table+count)) 1 = some code)
    (retRead : (d.dmem.storeInt (.ofNat 64 state) 1 ((count : Int)+1)).loadInt d.regs.rsp.toBitVec 8 =
      some (ra.toNat : Int))
    (P : MachineState → Prop)
    (finish : ∀ t, Returned ⟨d,allocEntry+7⟩ t ra →
      t.data.dmem = d.dmem.storeInt (.ofNat 64 state) 1 ((count : Int)+1) →
      t.data.regs.rax.toNat = (if code = 1 then slot count else 0) → P t) :
    Eventually (instructionStep fetch) P ⟨d,allocEntry+7⟩ := by
  have target : label "L_ffffffff81196d54" = allocEntry + 7 + 3 + 3 + 2 + 7 + 3 + 2 + 8 + 8 + 8 + 1 := by
    decide +kernel
  simp only [slots] at small
  have cases : count = 0 ∨ count = 1 ∨ count = 2 ∨ count = 3 ∨ count = 4 ∨ count = 5 ∨ count = 6 ∨
      count = 7 := by omega
  rcases binary with rfl | rfl
  · rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [state, table] at stateRead tableRead retRead
      stub_prefix agree cache stateRead tableRead
      rw [branch_taken (by decide), target]
      simp only [Effects.All]
      stub_instr agree
      intro undefined
      stub_instr agree
      stub_load retRead
      apply Eventually.done
      apply finish
      · simp [Returned, return_pc]
      · rfl
      · simp
  · rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [state, table] at stateRead tableRead retRead
      stub_prefix agree cache stateRead tableRead
      rw [branch_skipped (by decide)]
      simp only [Effects.All]
      stub_instr agree
      simp [BitVec.signed]
      stub_instr agree
      simp [BitVec.signed]
      stub_instr agree
      simp [BitVec.signed]
      stub_instr agree
      stub_load retRead
      apply Eventually.done
      apply finish
      · simp [Returned, return_pc]
      · rfl
      · simp [slot, objects]
        rfl

/-- The release stub, executed: it returns and changes nothing. -/
theorem free_run (agree : ∀ pc i, Witness.fetch pc = some i → fetch pc = some i)
    (d : MachineData) (ra : UInt64)
    (retRead : d.dmem.loadInt d.regs.rsp.toBitVec 8 = some (ra.toNat : Int))
    (P : MachineState → Prop)
    (finish : ∀ t, Returned ⟨d,freeEntry⟩ t ra → t.data.dmem = d.dmem → P t) :
    Eventually (instructionStep fetch) P ⟨d,freeEntry⟩ := by
  stub_instr agree
  stub_load retRead
  apply Eventually.done
  apply finish
  · simp [Returned, return_pc]
  · rfl

/-! ## Ranges below the stack pointer -/

theorem low_scratch (x a : BitVec 64) (inside : InRange (x - 8 - 8) 8 a) : InRange (x - 16) 16 a := by
  obtain ⟨i,bound,rfl⟩ := inside
  exact ⟨i,by omega,by bv_omega⟩

theorem high_scratch (x a : BitVec 64) (inside : InRange (x - 8) 8 a) : InRange (x - 16) 16 a := by
  obtain ⟨i,bound,rfl⟩ := inside
  refine ⟨8+i,by omega,?_⟩
  rw [BitVec.ofNat_add]
  bv_omega

theorem return_apart (x a : BitVec 64) (inside : InRange x 8 a) : ¬InRange (x - 16) 16 a := by
  intro scratch
  have top : x - 16 + .ofNat 64 16 = x := by bv_omega
  exact InRange.offset_disjoint (x - 16) 16 8 0 16 (by omega) (by omega) (.inr (by omega)) a
    (by rwa [top]) (by simpa using scratch)

theorem writes_bytes {c : Context} {a : BitVec 64} (write : c.writes a) : c.bytes a :=
  .inr (.inr ⟨write.1,.inr write.2⟩)

/-! ## The `alloc` clause, with what the active half needs kept -/

/-- The allocation stub from any entry state the contract admits: the
clause's conclusion, and besides it the saved `rdi` still in the scratch at
the return and the callback's exact effect on the bytes of the coverage
buffer. -/
theorem alloc_strong (agree : ∀ pc i, Witness.fetch pc = some i → fetch pc = some i)
    (tracePc : TracePcContract fetch) (tableAt : Nat) (peers : List (PeerId × Nat))
    (c : Context) (d : MachineData) (ra : UInt64) (live : List Nat) (record : HiddenRecord)
    (stream : List HiddenRecord)
    (frame : EntryFrame ⟨d,allocEntry⟩ ra)
    (ready : ServiceReady (layout tableAt peers) allocator c ⟨d,allocEntry⟩)
    (cache : d.regs.rdi.toNat = state)
    (idle : Idle d.dmem live (record :: stream)) :
    Eventually (instructionStep fetch) (fun t =>
      Returned ⟨d,allocEntry⟩ t ra ∧
      EqualOutside (ServiceWrites (layout tableAt peers) allocator c ⟨d,allocEntry⟩ live) d.dmem t.data.dmem ∧
      c.At t.data.dmem ∧ AllocResult (layout tableAt peers) allocator live record stream t ∧
      t.data.dmem.loadInt (d.regs.rsp.toBitVec - 8) 8 = some (d.regs.rdi.toNat : Int) ∧
      ∃ tc : MachineState, KcovEffect .pc (entered d) tc ∧ c.At (entered d).data.dmem ∧
        EntryFrame (entered d) (allocEntry+1+5).toUInt64 ∧
        (∀ a, c.writes a → t.data.dmem.get? a = tc.data.dmem.get? a) ∧
        (∀ a, c.writes a → d.dmem.get? a = (entered d).data.dmem.get? a)) ⟨d,allocEntry⟩ := by
  have sep := ready.separated
  have scratchOf : ∀ a, InRange (d.regs.rsp.toBitVec - 16) 16 a →
      Scratch ⟨d,allocEntry⟩ allocator.depth a := fun _ h => h
  have stackCoverage : ∀ a, InRange (d.regs.rsp.toBitVec - 16) 16 a → ¬c.bytes a :=
    fun a h => sep.stackCoverage a (.inl (scratchOf a h))
  have stackArena : ∀ a, InRange (d.regs.rsp.toBitVec - 16) 16 a → ¬(layout tableAt peers).Arena a :=
    fun a h => sep.stackArena a (.inl (scratchOf a h))
  have byteMapped : ∀ i < 16, (d.dmem.get? (d.regs.rsp.toBitVec - 16 + .ofNat 64 i)).isSome = true :=
    ready.stackMapped
  have mappedHigh : (d.dmem.loadInt (d.regs.rsp.toBitVec - 8) 8).isSome = true := by
    rw [loadInt_defined]
    intro i bound
    have same : d.regs.rsp.toBitVec - 8 + .ofNat 64 i = d.regs.rsp.toBitVec - 16 + .ofNat 64 (8+i) := by
      rw [BitVec.ofNat_add]
      bv_omega
    rw [same]
    exact byteMapped (8+i) (by omega)
  have mappedLow : (d.dmem.loadInt (d.regs.rsp.toBitVec - 8 - 8) 8).isSome = true := by
    rw [loadInt_defined]
    intro i bound
    have same : d.regs.rsp.toBitVec - 8 - 8 + .ofNat 64 i = d.regs.rsp.toBitVec - 16 + .ofNat 64 i := by
      bv_omega
    rw [same]
    exact byteMapped i (by omega)
  have callsReady : CallsReady c (pushed d) := {
    state := state_frame c d.dmem _ ready.coverage _ (storeInt_frame d.dmem _ 8 _)
      (fun a h written => stackCoverage a (high_scratch _ a written) h)
    aligned := aligned_sub d.regs.rsp 8 frame.1 (by decide)
    mapped := storeInt_defined _ _ _ _ _ _ mappedLow
    pushSeparate := fun a h written => stackCoverage a (low_scratch _ a written) h
    returnSeparate := fun a h written => stackCoverage a (low_scratch _ a written) (writes_bytes h)
    metadataSeparate := fun a h => (sep.bufferMetadata a h).1
    preemptSeparate := fun a h => (sep.bufferMetadata a h).2 }
  have enteredReady := called_ready c (pushed d) (allocEntry+1+5) (label target) callsReady
  apply front agree tracePc c d mappedHigh callsReady
    (fun a h written => stackCoverage a (high_scratch _ a written) (writes_bytes h))
  intro u tc sp di bx bp r12 r13 r14 r15 memoryU stateU savedRead frameU effect
  -- memory at the body's entry is the entry memory outside the scratch and the buffer
  have toEntered : EqualOutside (InRange (d.regs.rsp.toBitVec - 16) 16) d.dmem (entered d).data.dmem := by
    intro a outside
    exact ((storeInt_frame d.dmem (d.regs.rsp.toBitVec - 8) 8 _) a
      (fun h => outside (high_scratch _ a h))).trans
      ((storeInt_frame (pushed d).dmem (d.regs.rsp.toBitVec - 8 - 8) 8 _) a
        (fun h => outside (low_scratch _ a h)))
  have toBody : EqualOutside (fun a => InRange (d.regs.rsp.toBitVec - 16) 16 a ∨ c.writes a) d.dmem u.dmem :=
    toEntered.trans frameU
  have arenaSame : ∀ a, (layout tableAt peers).Arena a → d.dmem.get? a = u.dmem.get? a := by
    intro a arena
    refine toBody a (fun h => ?_)
    rcases h with h | h
    · exact stackArena a h arena
    · exact sep.coverageArena a (writes_bytes h) arena
  obtain ⟨count,stateRead,room,before,after,outcomes,zeroed,lives⟩ :=
    idle_frame (tableAt := tableAt) (peers := peers) idle (fun a arena _ => arenaSame a arena)
  have small : count < slots := by
    simp only [List.length_cons] at room
    omega
  have before' : u.dmem.get? (BitVec.ofNat 64 state - 1#64) = none := by
    rw [state_before]
    exact before
  have after' : u.dmem.get? (BitVec.ofNat 64 state + 1#64) = none := by
    rw [state_after]
    exact after
  have rdi : u.regs.rdi = UInt64.ofNat state := by
    rw [di, ← cache, UInt64.ofNat_toNat]
  have code : Stub.outcome record = 0 ∨ Stub.outcome record = 1 := by
    unfold Stub.outcome
    split
    · exact .inr rfl
    · exact .inl rfl
  have returnWord : u.dmem.loadInt u.regs.rsp.toBitVec 8 = some (ra.toNat : Int) := by
    rw [sp, ← toBody.loadInt d.regs.rsp.toBitVec 8 (fun i bound h => by
      rcases h with h | h
      · exact return_apart _ _ ⟨i,bound,rfl⟩ h
      · exact sep.stackCoverage _ (.inr ⟨i,bound,rfl⟩) (writes_bytes h))]
    exact frame.2
  apply body_run agree u ra count small (Stub.outcome record) code rdi stateRead
  · have old := outcomes 0 (by simp)
    unfold Mem.loadInt at old ⊢
    rw [away u.dmem _ _ 1 (by simp only [table, state]; omega) (by simp only [table, slots] at *; omega)]
    simpa using old
  · rw [read_kept _ before' after' (by decide) (by rw [returnWord]; rfl)]
    exact returnWord
  intro t returned memory result
  have earlier : ∀ object ∈ live, ∃ index < count+1, object = slot index := fun object member =>
    let ⟨index,bound,equal⟩ := lives object member
    ⟨index,by omega,equal⟩
  have stateArena : ∀ a, InRange (BitVec.ofNat 64 state) 1 a → (layout tableAt peers).Arena a := by
    rintro a ⟨j,one,rfl⟩
    have zero : j = 0 := by omega
    subst zero
    rw [← BitVec.ofNat_add]
    exact arena_contains (by decide) (by decide)
  obtain ⟨pcT,spT,bxT,bpT,r12T,r13T,r14T,r15T⟩ := returned
  refine ⟨⟨pcT,spT.trans (congrArg (· + 8) sp),bxT.trans bx,bpT.trans bp,r12T.trans r12,r13T.trans r13,
    r14T.trans r14,r15T.trans r15⟩,?_,?_,⟨fun failure => ?_,fun success => ?_⟩,?_,
    tc,effect,enteredReady.2,enteredReady.1,?_,?_⟩
  · rw [memory]
    intro a outside
    refine (toBody a (fun h => outside ?_)).trans
      (storeInt_frame u.dmem _ 1 _ a (fun inside => outside (.inr (.inl ?_))))
    · rcases h with h | h
      · exact .inl (scratchOf a h)
      · exact .inr (.inr h)
    · obtain ⟨j,one,rfl⟩ := inside
      have zero : j = 0 := by omega
      subst zero
      rw [← BitVec.ofNat_add]
      exact ⟨arena_contains (by decide) (by decide),not_kept lives (by omega) (.inl (by decide))⟩
  · rw [memory]
    exact coverage_kept _ before' after' stateU
  · have zero : Stub.outcome record = 0 := by simp [Stub.outcome, failure]
    rw [zero] at result
    refine ⟨by simpa using result,?_⟩
    rw [memory]
    exact idle_advance room before after outcomes zeroed earlier
  · have one : Stub.outcome record = 1 := by simp [Stub.outcome, success]
    rw [one] at result
    have address : t.data.regs.rax.toNat = slot count := by simpa using result
    show t.data.regs.rax.toNat ≠ 0 ∧ _
    rw [address]
    simp only [slots] at small
    refine ⟨by simp only [slot, objects]; omega,by simp only [slot, objects]; omega,
      by simp only [slot, objects, nodeSize]; omega,
      ⟨(arenaBase,arenaSize),List.mem_singleton.mpr rfl,
        by simp only [slot, objects, arenaBase]; omega,
        by simp only [slot, objects, arenaBase, arenaSize, nodeSize]; omega⟩,?_,?_,?_⟩
    · intro other member
      obtain ⟨index,bound,rfl⟩ := lives other member
      show disjointRanges (slot count) nodeSize (slot index) nodeSize = true
      have apart : slot index + nodeSize ≤ slot count := by
        simp only [slot, objects, nodeSize]
        omega
      simp [disjointRanges, apart]
    · have old := zeroed 0 (by simp) (by simpa using success)
      simp only [readNat, memory] at old ⊢
      rw [away u.dmem _ _ nodeSize (by simp only [slot, objects, state]; omega)
        (by simp only [slot, objects, nodeSize]; omega)]
      simpa using old
    · rw [memory]
      refine idle_advance room before after outcomes zeroed (fun object member => ?_)
      rcases List.mem_append.mp member with old | new
      · exact earlier object old
      · exact ⟨count,by omega,List.mem_singleton.mp new⟩
  · rw [memory, read_kept _ before' after' (by decide) (by rw [savedRead]; rfl)]
    exact savedRead
  · intro a written
    rw [memory, ← memoryU]
    exact (storeInt_frame u.dmem _ 1 _ a (fun inside =>
      sep.coverageArena a (writes_bytes written) (stateArena a inside))).symm
  · intro a written
    exact toEntered a (fun h => stackCoverage a h (writes_bytes written))

/-! ## The contract -/

/-- The `free` clause: package 4's, for this decoder and this scratch. -/
theorem free_clause (agree : ∀ pc i, Witness.fetch pc = some i → fetch pc = some i)
    (tableAt : Nat) (peers : List (PeerId × Nat)) (c : Context) (s : MachineState) (ra : UInt64)
    (live : List Nat) (stream : List HiddenRecord)
    (entry : s.pc = freeEntry) (frame : EntryFrame s ra)
    (ready : ServiceReady (layout tableAt peers) allocator c s)
    (idle : Idle s.data.dmem live stream) :
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧
      EqualOutside (ServiceWrites (layout tableAt peers) allocator c s
        (live.erase s.data.regs.rsi.toNat)) s.data.dmem t.data.dmem ∧
      c.At t.data.dmem ∧ Idle t.data.dmem (live.erase s.data.regs.rsi.toNat) stream) s := by
  obtain ⟨d,pc⟩ := s
  change pc = _ at entry
  subst entry
  apply free_run agree d ra frame.2
  intro t returned memory
  obtain ⟨count,stateRead,room,before,after,outcomes,zeroed,lives⟩ := idle
  refine ⟨returned,?_,?_,?_⟩
  · rw [memory]
    exact fun _ _ => rfl
  · rw [memory]
    exact ready.coverage
  · rw [memory]
    exact ⟨count,stateRead,room,before,after,outcomes,zeroed,
      fun object member => lives object (List.mem_of_mem_erase member)⟩

/-- THE ACTIVE STUB MEETS THE CONTRACT AS SIGNED, at any decoder that holds
its code and whose PC callback meets the landed contract. -/
theorem contract (agree : ∀ pc i, Witness.fetch pc = some i → fetch pc = some i)
    (tracePc : TracePcContract fetch) (tableAt : Nat) (peers : List (PeerId × Nat)) :
    AllocatorContract fetch (Stub.layout tableAt peers) allocator :=
  ⟨fun _ _ _ _ idle same => idle_frame idle same,
   fun c s ra live record stream entry frame ready cache _ _ idle => by
     obtain ⟨d,pc⟩ := s
     change pc = _ at entry
     subst entry
     exact eventually_weaken (instructionStep fetch) _ _ _ (fun t h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩)
       (alloc_strong agree tracePc tableAt peers c d ra live record stream frame ready cache idle),
   fun c s ra live stream entry frame ready _ _ _ idle =>
     free_clause agree tableAt peers c s ra live stream entry frame ready idle⟩

/-! ## The stub is active -/

/-- Memories that agree on a predicate's bytes agree on a read inside it. -/
theorem loadInt_same {m m' : Mem 64} {inside : BitVec 64 → Prop}
    (same : ∀ a, inside a → m.get? a = m'.get? a) (base : BitVec 64) (n : Nat)
    (within : ∀ i < n, inside (base + .ofNat 64 i)) : m.loadInt base n = m'.loadInt base n :=
  EqualOutside.loadInt (writes := fun a => ¬inside a)
    (fun a outside => same a (Classical.not_not.mp outside)) base n (fun i bound h => h (within i bound))

/-- THE STUB USES ITS SCRATCH AND WRITES THE BUFFER. From an entry state the
`alloc` clause admits, with the coverage buffer in use in PC mode and room
for a record, and a word below the return word that is not already the
cache pointer, the stub returns having changed a byte of its scratch and a
byte of the coverage buffer. -/
theorem alloc_active (agree : ∀ pc i, Witness.fetch pc = some i → fetch pc = some i)
    (tracePc : TracePcContract fetch) (tableAt : Nat) (peers : List (PeerId × Nat))
    (c : Context) (s : MachineState) (ra : UInt64) (live : List Nat) (record : HiddenRecord)
    (stream : List HiddenRecord)
    (entry : s.pc = allocEntry) (frame : EntryFrame s ra)
    (ready : ServiceReady (Stub.layout tableAt peers) allocator c s)
    (cache : s.data.regs.rdi.toNat = (Stub.layout tableAt peers).cache)
    (idle : Stub.Idle s.data.dmem live (record :: stream))
    (needed : c.Needed) (mode : c.coverage.mode = 2)
    (count : Nat) (header : load64 s.data.dmem c.coverage.area = some (.ofNat 64 count))
    (room : count + 1 < c.coverage.capacity.toNat)
    (saved : s.data.dmem.loadInt (s.data.regs.rsp.toBitVec - 8) 8 ≠ some (s.data.regs.rdi.toNat : Int)) :
    Eventually (instructionStep fetch) (fun t => Returned s t ra ∧
      (∃ a, Scratch s allocator.depth a ∧ s.data.dmem.get? a ≠ t.data.dmem.get? a) ∧
      (∃ a, c.writes a ∧ s.data.dmem.get? a ≠ t.data.dmem.get? a)) s := by
  obtain ⟨d,pc⟩ := s
  change pc = _ at entry
  subst entry
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (alloc_strong agree tracePc tableAt peers c d ra live record stream frame ready cache idle)
  rintro t ⟨returned,-,-,-,savedAfter,tc,effect,stateE,entryE,afterSame,beforeSame⟩
  refine ⟨returned,?_,?_⟩
  · apply Classical.byContradiction
    intro none
    have same : ∀ a, Scratch ⟨d,allocEntry⟩ allocator.depth a → d.dmem.get? a = t.data.dmem.get? a :=
      fun a h => Classical.not_not.mp (fun ne => none ⟨a,h,ne⟩)
    have equal := loadInt_same same (d.regs.rsp.toBitVec - 8) 8
      (fun i bound => high_scratch _ _ ⟨i,bound,rfl⟩)
    exact saved (equal.trans savedAfter)
  · apply Classical.byContradiction
    intro none
    have same : ∀ a, c.writes a → d.dmem.get? a = t.data.dmem.get? a :=
      fun a h => Classical.not_not.mp (fun ne => none ⟨a,h,ne⟩)
    have headerBytes : ∀ i < 8, c.writes (c.coverage.area + .ofNat 64 i) :=
      fun i bound => ⟨needed,i,by omega,rfl⟩
    have capacityBound := c.coverage.capacity.isLt
    have active : Kcov.enabled .pc c.coverage c.preempt = true :=
      (LookupCoverage.enabled_iff .pc c.coverage c.preempt).mpr ⟨needed.1,by simpa using mode⟩
    obtain ⟨-,-,count',bound',header',plan⟩ := active_plan c .pc (entered d) _ stateE
      (return_read entryE) active
    -- the header the callback reads is the entry state's
    have atEntry := loadInt_same beforeSame c.coverage.area 8 headerBytes
    have counts : count' = count := by
      have both : (some (BitVec.ofNat 64 count) : Option (BitVec 64)) = some (.ofNat 64 count') := by
        rw [← header, ← header']
        simp only [load64]
        rw [show Mem.loadInt d.dmem c.coverage.area 8 = _ from atEntry]
      have numbers := congrArg BitVec.toNat (Option.some.inj both)
      simp only [BitVec.toNat_ofNat] at numbers
      omega
    subst counts
    -- the callback stores the incremented header, then the record
    obtain ⟨stores,computed,memory⟩ := effect
    rw [plan] at computed
    cases Option.some.inj computed
    simp only [Kcov.bufferPlan, ↓reduceIte, room, List.foldl_cons, List.foldl_nil] at memory
    have after : tc.data.dmem.loadInt c.coverage.area 8 =
        some ((BitVec.ofNat 64 (count' + 1)).toNat : Int) := by
      rw [memory, ← (storeInt_frame _ (c.coverage.area + .ofNat 64 (8 * (count' + 1))) 8 _).loadInt
        c.coverage.area 8 (fun i bound inside => InRange.offset_disjoint c.coverage.area
          (8 * (count' + 1)) 8 0 8 (by omega) (by omega) (.inr (by omega)) _ inside
          ⟨i,bound,by simp⟩)]
      exact load64_store _ _ _
    have final : t.data.dmem.loadInt c.coverage.area 8 = _ :=
      (loadInt_same afterSame c.coverage.area 8 headerBytes).trans after
    have equal := loadInt_same same c.coverage.area 8 headerBytes
    have read : load64 d.dmem c.coverage.area = some (.ofNat 64 (count' + 1)) := by
      simp only [load64]
      rw [show Mem.loadInt d.dmem c.coverage.area 8 = _ from equal.trans final]
      rw [Option.map_some, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [header] at read
    have numbers := congrArg BitVec.toNat (Option.some.inj read)
    simp only [BitVec.toNat_ofNat] at numbers
    omega

#print axioms contract
#print axioms alloc_active
end Binary.Statements.C1.Witness
