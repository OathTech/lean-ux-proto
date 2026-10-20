import PairInsertCallback
import PairInsertWalkRegions
import PairInsertCompareRegions
import PairInsertArguments

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage
local instance : Labels := Image.linkedLabels

def walkPC (locked : Bool) (offset : Nat) : Int64 :=
  codeEntry+(if locked then 0x65 else 0)+.ofNat offset

inductive WalkTrace where | entry | present | mismatch | empty | finish

def WalkTrace.offset : WalkTrace → Nat
  | .entry => 0x8d | .present => 0xa0 | .mismatch => 0xb9 | .empty => 0xc7 | .finish => 0xcc

theorem walk_trace_fetch (locked : Bool) (site : WalkTrace) :
    IndexInsertImage.Insert.fetch (walkPC locked site.offset)=
      some ⟨Instrumentation.callInstruction "L_ffffffff810f31f0",5⟩ := by
  cases locked <;> cases site <;> rfl

theorem Core.same {n o c initial ra p shadow s t}
    (core : Core n o c initial ra p shadow s)
    (regs : t.regs=s.regs) (heap : t.dmem=s.dmem) : Core n o c initial ra p shadow t :=
  ⟨by rw [regs]; exact core.stack,by rw [regs]; exact core.table,
   by rw [regs]; exact core.owner,heap ▸ core.memory,heap ▸ core.frame,heap ▸ core.outside⟩

theorem walk_cursor (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) {n o c initial ra p shadow s}
    (facts : FrameFacts n o c initial ra) (core : Core n o c initial ra p shadow s) (locked : Bool) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=walkPC locked 0x9b ∧ Core n o c initial ra p shadow t.data ∧
      t.data.regs.rbx=s.regs.rbx-8 ∧ t.data.regs.r13=s.regs.r13 ∧
      t.data.regs.r14=s.regs.r14 ∧ t.data.regs.r15=s.regs.r15) ⟨s,walkPC locked 0x92⟩ := by
  obtain ⟨old,mapped⟩ := Option.isSome_iff_exists.mp (core.calls facts).mapped
  apply core.region_callback fetch (.ofNat 0xffffffff810f31f0) (walkPC locked 0x9b) .pc trace facts
    (walkPC locked 0x92) {s.regs with rbx := s.regs.rbx-8} rfl rfl
  cases locked with
  | false =>
    exact region_eventually (IndexInsertImage.Insert_r92_layout.agreement decoder) s _
      (cursor_call 0x92 s old mapped)
  | true =>
    exact region_eventually (IndexInsertImage.Insert_rf7_layout.agreement decoder) s _
      (cursor_call 0xf7 s old mapped)

theorem walk_guard (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    {n o c initial ra p shadow s} (core : Core n o c initial ra p shadow s) (locked : Bool)
    (nonzero : s.regs.rbx.toBitVec≠0) :
    Eventually (instructionStep fetch) (fun t => t.pc=walkPC locked 0xa0 ∧
      Core n o c initial ra p shadow t.data ∧ t.data.regs=s.regs) ⟨s,walkPC locked 0x9b⟩ := by
  have region : Eventually (instructionStep fetch) (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem ∧
      t.pc=(if s.regs.rbx.toBitVec=0 then walkPC locked 0xcc else walkPC locked 0xa0))
      ⟨s,walkPC locked 0x9b⟩ := by
    cases locked with
    | false => exact region_eventually (IndexInsertImage.Insert_r9b_layout.agreement decoder) s _ (first_node_guard s)
    | true => exact region_eventually (IndexInsertImage.Insert_r100_layout.agreement decoder) s _ (second_node_guard s)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ region
  rintro t ⟨regs,heap,pc⟩
  exact ⟨by simpa only [ite_eq_right nonzero] using pc,core.same regs heap,regs⟩

def argumentRegisters (locked : Bool) (s : MachineData) (index : UInt32) : Reg64s :=
  if locked then {s.regs with
    r15 := .ofNat index.toNat,rdi := .ofNat (s.regs.get (.low .r13 .W32)).toNat,rsi := .ofNat index.toNat}
  else {s.regs with
    r14 := .ofNat index.toNat,rdi := .ofNat (s.regs.get (.low .r13 .W32)).toNat,rsi := .ofNat index.toNat}

theorem walk_arguments (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (cmp : TraceCmp4Contract fetch) {n o c initial ra p shadow s}
    (facts : FrameFacts n o c initial ra) (core : Core n o c initial ra p shadow s)
    (locked : Bool) (index : UInt32) (read : s.dmem.loadInt (s.regs.rbx.toBitVec+28) 4=some index.toNat) :
    Eventually (instructionStep fetch) (fun t => t.pc=walkPC locked 0xb4 ∧
      Core n o c initial ra p shadow t.data ∧ t.data.regs.rbx=s.regs.rbx ∧
      t.data.regs.r13=s.regs.r13 ∧ t.data.regs.r14=(argumentRegisters locked s index).r14 ∧
      t.data.regs.r15=(argumentRegisters locked s index).r15) ⟨s,walkPC locked 0xa5⟩ := by
  obtain ⟨old,mapped⟩ := Option.isSome_iff_exists.mp (core.calls facts).mapped
  have prepare : Eventually (instructionStep fetch) (fun t =>
      t.data.regs={argumentRegisters locked s index with rsp := s.regs.rsp-8} ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 (walkPC locked 0xb4).toBitVec.toInt ∧
      t.pc=.ofNat 0xffffffff810f4080) ⟨s,walkPC locked 0xa5⟩ := by
    cases locked with
    | false =>
      exact region_eventually (IndexInsertImage.Insert_ra5_layout.agreement decoder) s _
        (first_arguments s index old read mapped)
    | true =>
      exact region_eventually (IndexInsertImage.Insert_r10a_layout.agreement decoder) s _
        (second_arguments s index old read mapped)
  have run := core.region_callback fetch (.ofNat 0xffffffff810f4080) (walkPC locked 0xb4) .cmp4 cmp facts
    (walkPC locked 0xa5) (argumentRegisters locked s index)
    (by cases locked <;> rfl) (by cases locked <;> rfl) prepare
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨pc,core,bx,r13,r14,r15⟩
  refine ⟨pc,core,?_,?_,r14,r15⟩
  · cases locked <;> exact bx
  · cases locked <;> exact r13

#print axioms walk_trace_fetch
#print axioms walk_cursor
#print axioms walk_guard
#print axioms walk_arguments
end Binary.Pair.Insert
