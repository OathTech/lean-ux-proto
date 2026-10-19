import WordAlignment
import PeerCall

set_option maxHeartbeats 1000000

namespace Binary.PeerGet
open TrustBase
local instance : Labels := Image.linkedLabels

/-- Physical postcondition shared by instrumentation calls. Caller-save
    argument registers and flags are intentionally not constrained. -/
def CallPost (s : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (returnOffset : Nat) (t : MachineState) : Prop :=
  t.pc = Image.PeerGet.entry + .ofNat returnOffset ∧
  t.data.regs.rsp = s.regs.rsp ∧
  t.data.regs.rbx = s.regs.rbx ∧ t.data.regs.rbp = s.regs.rbp ∧
  t.data.regs.r12 = s.regs.r12 ∧ t.data.regs.r13 = s.regs.r13 ∧
  t.data.regs.r14 = s.regs.r14 ∧ t.data.regs.r15 = s.regs.r15 ∧
  KcovState coverage preempt t.data.dmem ∧
  EqualOutside (fun address => InRange (s.regs.rsp.toBitVec-8) 8 address ∨
    KcovBufferBytes coverage address) s.dmem t.data.dmem ∧
  t.data.dmem.loadInt (s.regs.rsp.toBitVec-8) 8 =
    some ((Image.PeerGet.entry + .ofNat returnOffset).toUInt64.toNat : Int)

/-- A proof-local bundle of the concrete obligations already used above.
    This is carried from execution, not assumed afresh at successive calls. -/
structure CallsReady (coverage : KcovLayout) (preempt : BitVec 32) (s : MachineData) : Prop where
  state : KcovState coverage preempt s.dmem
  aligned : s.regs.rsp.toNat % 8 = 0
  mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true
  pushSeparate : ∀ a, KcovStateBytes coverage a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a
  returnSeparate : KcovSeparated coverage (InRange (s.regs.rsp.toBitVec-8) 8)
  metadataSeparate : KcovSeparated coverage (KcovMetadataBytes coverage)
  preemptSeparate : KcovSeparated coverage (InRange preemptCountAddress 4)

/-- Instructions that leave memory and SP unchanged preserve callback
    readiness, regardless of their temporary registers or undefined flags. -/
theorem CallsReady.congr {coverage : KcovLayout} {preempt : BitVec 32}
    {before after : MachineData} (ready : CallsReady coverage preempt before)
    (memory : after.dmem = before.dmem) (stack : after.regs.rsp = before.regs.rsp) :
    CallsReady coverage preempt after := by
  exact {
    state := by simpa only [memory] using ready.state
    aligned := by simpa only [stack] using ready.aligned
    mapped := by simpa only [memory, stack] using ready.mapped
    pushSeparate := by simpa only [stack] using ready.pushSeparate
    returnSeparate := by simpa only [stack] using ready.returnSeparate
    metadataSeparate := ready.metadataSeparate
    preemptSeparate := ready.preemptSeparate }

#print axioms CallsReady.congr

theorem CallPost.next_ready {s : MachineData} {coverage preempt offset t}
    (post : CallPost s coverage preempt offset t) (ready : CallsReady coverage preempt s) :
    CallsReady coverage preempt t.data := by
  obtain ⟨_, sp, _, _, _, _, _, _, state, _, word⟩ := post
  refine ⟨state, ?_, ?_, ?_, ?_, ready.metadataSeparate, ready.preemptSeparate⟩
  · simpa only [sp] using ready.aligned
  · rw [sp, word]
    rfl
  · simpa only [sp] using ready.pushSeparate
  · simpa only [sp] using ready.returnSeparate

theorem CallPost.trans {s : MachineData} {coverage preempt offset₁ offset₂ t u}
    (first : CallPost s coverage preempt offset₁ t)
    (second : CallPost t.data coverage preempt offset₂ u) :
    CallPost s coverage preempt offset₂ u := by
  obtain ⟨_, sp₁, bx₁, bp₁, r12₁, r13₁, r14₁, r15₁, _, frame₁, _⟩ := first
  obtain ⟨pc, sp₂, bx₂, bp₂, r12₂, r13₂, r14₂, r15₂, state, frame₂, word⟩ := second
  refine ⟨pc, sp₂.trans sp₁, bx₂.trans bx₁, bp₂.trans bp₁, r12₂.trans r12₁,
    r13₂.trans r13₁, r14₂.trans r14₁, r15₂.trans r15₁, state, ?_, ?_⟩
  · rw [sp₁] at frame₂
    intro address outside
    exact (frame₁ address outside).trans (frame₂ address outside)
  · simpa only [sp₁] using word

/-- The service part after an actual CALL has established its pushed word.
    Region proofs establish `regs` and `memory`; this lemma does not assume
    that the CALL instruction can execute from an unmapped stack. -/
theorem after_call (fetch : Int64 → Option Decoded) (address : Int64) (kind : KcovKind)
    (contract : ServiceReturns fetch address (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (s : MachineData) (callee : MachineState) (returnOffset : Nat)
    (regs : callee.data.regs = {s.regs with rsp := s.regs.rsp-8})
    (memory : callee.data.dmem = callMemory s returnOffset) (pc : callee.pc = address)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (state : KcovState coverage preempt s.dmem)
    (aligned : s.regs.rsp.toNat % 8 = 0)
    (pushSeparate : ∀ a, KcovStateBytes coverage a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a)
    (returnSeparate : KcovSeparated coverage (InRange (s.regs.rsp.toBitVec-8) 8))
    (metadataSeparate : KcovSeparated coverage (KcovMetadataBytes coverage))
    (preemptSeparate : KcovSeparated coverage (InRange preemptCountAddress 4)) :
    Eventually (instructionStep fetch) (CallPost s coverage preempt returnOffset) callee := by
  have pushed := storeInt_frame s.dmem (s.regs.rsp.toBitVec - 8) 8
    (Image.PeerGet.entry + .ofNat returnOffset).toBitVec.toInt
  have calleeState : KcovState coverage preempt callee.data.dmem := by
    rw [memory]
    exact Kcov.state_frame coverage preempt _ _ state _ pushed pushSeparate
  have calleeSP : callee.data.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 8 := by simp [regs]
  have entry : EntryFrame callee (Image.PeerGet.entry + .ofNat returnOffset).toUInt64 := by
    constructor
    · simp only [regs]
      change (s.regs.rsp - 8).toNat % 8 = 0
      exact aligned_sub _ 8 aligned (by decide)
    · rw [calleeSP, memory]
      change (callMemory s returnOffset).loadInt (s.regs.rsp.toBitVec-8) 8 = _
      have stored := load64_store s.dmem (s.regs.rsp.toBitVec-8)
        (Image.PeerGet.entry + .ofNat returnOffset).toBitVec
      exact stored
  have returned := Kcov.callback_endpoint fetch address kind contract
    coverage preempt callee (Image.PeerGet.entry + .ofNat returnOffset).toUInt64 pc entry calleeState
    (by simpa only [calleeSP] using returnSeparate) metadataSeparate preemptSeparate
  apply eventually_weaken (instructionStep fetch) _ _ _ _ returned
  rintro t ⟨ret, state, frame⟩
  obtain ⟨returnPC, rsp, rbx, rbp, r12, r13, r14, r15⟩ := ret
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, state, ?_, ?_⟩
  · simpa using returnPC
  · rw [rsp, regs]
    apply UInt64.toBitVec_inj.mp
    change (s.regs.rsp.toBitVec - 8) + 8 = s.regs.rsp.toBitVec
    exact BitVec.sub_add_cancel _ _
  · simpa only [regs] using rbx
  · simpa only [regs] using rbp
  · simpa only [regs] using r12
  · simpa only [regs] using r13
  · simpa only [regs] using r14
  · simpa only [regs] using r15
  · rw [memory] at frame
    exact pushed.trans frame
  · have unchanged := frame.loadInt (s.regs.rsp.toBitVec-8) 8 (by
      intro byte bound written
      exact returnSeparate _ written ⟨byte, bound, rfl⟩)
    have word := entry.2
    rw [calleeSP] at word
    exact unchanged.symm.trans word


/-- Compose a proved comparison-argument region with its named service
    contract. Each use supplies the actual decoded region's execution lemma. -/
theorem comparison_region (fetch : Int64 → Option Decoded)
    (code : List (Kraken.Sized Directive)) (offset returnOffset : Nat)
    (layout : LaidOut fetch (Image.PeerGet.entry + .ofNat offset) code)
    (contract : TraceConstCmp4Contract fetch) (s : MachineData) (arg1 arg2 : UInt64)
    (physicalRun : (run code offset s).All (fun t =>
      t.data.regs = {s.regs with rdi := arg1, rsi := arg2, rsp := s.regs.rsp-8} ∧
      t.data.dmem = callMemory s returnOffset ∧ t.pc = .ofNat 0xffffffff810f4100))
    (coverage : KcovLayout) (preempt : BitVec 32)
    (state : KcovState coverage preempt s.dmem)
    (aligned : s.regs.rsp.toNat % 8 = 0)
    (pushSeparate : ∀ a, KcovStateBytes coverage a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a)
    (returnSeparate : KcovSeparated coverage (InRange (s.regs.rsp.toBitVec-8) 8))
    (metadataSeparate : KcovSeparated coverage (KcovMetadataBytes coverage))
    (preemptSeparate : KcovSeparated coverage (InRange preemptCountAddress 4)) :
    Eventually (instructionStep fetch) (CallPost s coverage preempt returnOffset)
      ⟨s, Image.PeerGet.entry + .ofNat offset⟩ := by
  have executed := region_eventually layout s _ physicalRun
  apply eventually_trans (instructionStep fetch) _ _ _ executed
  rintro callee ⟨regs, memory, pc⟩
  let arguments : MachineData := {s with regs := {s.regs with rdi := arg1, rsi := arg2}}
  have returned := after_call fetch (.ofNat 0xffffffff810f4100) .constCmp4 contract
    arguments callee returnOffset (by simpa only [arguments] using regs)
    memory pc coverage preempt state aligned pushSeparate returnSeparate metadataSeparate preemptSeparate
  apply eventually_weaken (instructionStep fetch) _ _ _ _ returned
  intro t post
  simpa only [CallPost, arguments] using post

/-- The corresponding wrapper for a proved singleton trace-PC CALL. -/
theorem pc_region (fetch : Int64 → Option Decoded) (offset : Nat)
    (layout : LaidOut fetch (Image.PeerGet.entry + .ofNat offset) Image.PeerGet.r1b)
    (contract : TracePcContract fetch) (s : MachineData)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (state : KcovState coverage preempt s.dmem)
    (aligned : s.regs.rsp.toNat % 8 = 0)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true)
    (pushSeparate : ∀ a, KcovStateBytes coverage a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a)
    (returnSeparate : KcovSeparated coverage (InRange (s.regs.rsp.toBitVec-8) 8))
    (metadataSeparate : KcovSeparated coverage (KcovMetadataBytes coverage))
    (preemptSeparate : KcovSeparated coverage (InRange preemptCountAddress 4)) :
    Eventually (instructionStep fetch) (CallPost s coverage preempt (offset+5))
      ⟨s, Image.PeerGet.entry + .ofNat offset⟩ := by
  obtain ⟨word, wordRead⟩ := Option.isSome_iff_exists.mp mapped
  have executed := region_eventually layout s _ (trace_call offset s word wordRead)
  apply eventually_trans (instructionStep fetch) _ _ _ executed
  rintro callee ⟨regs, memory, pc⟩
  exact after_call fetch (.ofNat 0xffffffff810f31f0) .pc contract s callee (offset+5)
    regs memory pc coverage preempt state aligned pushSeparate returnSeparate
    metadataSeparate preemptSeparate

#print axioms CallPost.next_ready
#print axioms CallPost.trans
#print axioms pc_region

#print axioms comparison_region

#print axioms after_call

/-- Compose a proved register/memory-preserving branch with the actual PC
    instrumentation CALL at its successor. Flags may change in the branch. -/
theorem guard_pc_region (fetch : Int64 → Option Decoded)
    (code : List (Kraken.Sized Directive)) (offset nextOffset : Nat)
    (layout : LaidOut fetch (Image.PeerGet.entry + .ofNat offset) code)
    (nextLayout : LaidOut fetch (Image.PeerGet.entry + .ofNat nextOffset) Image.PeerGet.r1b)
    (contract : TracePcContract fetch) (s : MachineData)
    (physicalRun : (run code offset s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = Image.PeerGet.entry + .ofNat nextOffset))
    (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : CallsReady coverage preempt s) :
    Eventually (instructionStep fetch) (CallPost s coverage preempt (nextOffset+5))
      ⟨s, Image.PeerGet.entry + .ofNat offset⟩ := by
  have executed := region_eventually layout s _ physicalRun
  apply eventually_trans (instructionStep fetch) _ _ _ executed
  rintro guarded ⟨regs, memory, pc⟩
  have atNext : guarded = ⟨guarded.data, Image.PeerGet.entry + .ofNat nextOffset⟩ := by
    cases guarded with
    | mk data _ => exact congrArg (fun pc => (⟨data, pc⟩ : MachineState)) pc
  rw [atNext]
  have call := pc_region fetch nextOffset nextLayout contract guarded.data coverage preempt
    (by simpa only [memory] using ready.state)
    (by simpa only [regs] using ready.aligned)
    (by simpa only [regs, memory] using ready.mapped)
    (by simpa only [regs] using ready.pushSeparate)
    (by simpa only [regs] using ready.returnSeparate)
    ready.metadataSeparate ready.preemptSeparate
  apply eventually_weaken (instructionStep fetch) _ _ _ _ call
  intro t post
  simpa only [CallPost, regs, memory] using post

#print axioms guard_pc_region
end Binary.PeerGet
