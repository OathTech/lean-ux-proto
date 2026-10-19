import AllowedipsEntryMemory
import CommonBitsEntryHistory
import CommonBitsCallbackTrace
import AllowedipsOuterTrace
import AllowedipsLoopValues

namespace Binary.AllowedipsEntry
open TrustBase CommonBitsCoverage CommonBits
local instance : Labels := Image.linkedLabels

/-- Before the BH-disable store, only the actual stack and old-phase coverage
buffer can change. This narrower frame preserves input even if it aliases the
preempt word, which the function does not write until after consuming input. -/
def Writes (initial : MachineState) (coverage : KcovLayout) (old : BitVec 32)
    (a : BitVec 64) : Prop :=
  AllowedipsStackWrites initial a ∨ (Context.mk coverage old).writes a

structure At (initial : MachineState) (coverage : KcovLayout) (old : BitVec 32)
    (ra : UInt64) (s : MachineData) : Prop where
  stack : s.regs.rsp = initial.data.regs.rsp-80
  bx : s.regs.rbx = .ofBitVec ((initial.data.regs.get (.low .rsi .W32)).setWidth 64)
  bp : s.regs.rbp = initial.data.regs.rdx
  r12 : s.regs.r12 = .ofBitVec ((initial.data.regs.get (.low .rsi .W32)).setWidth 64)
  memory : MemoryAt initial coverage old ra s.dmem
  frame : EqualOutside (Writes initial coverage old) initial.data.dmem s.dmem

theorem At.ready {c coverage old ra initial world v s}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (state : At initial coverage old ra s) : CallsReady ⟨coverage,old⟩ s :=
  memory_ready pre s state.memory state.stack

theorem At.congr {initial coverage old ra before after}
    (state : At initial coverage old ra before) (memory : after.dmem=before.dmem)
    (stack : after.regs.rsp=before.regs.rsp) (bx : after.regs.rbx=before.regs.rbx)
    (bp : after.regs.rbp=before.regs.rbp) (r12 : after.regs.r12=before.regs.r12) :
    At initial coverage old ra after :=
  ⟨stack.trans state.stack,bx.trans state.bx,bp.trans state.bp,r12.trans state.r12,
   memory.symm ▸ state.memory, memory.symm ▸ state.frame⟩

theorem call_slot {initial coverage old ra s} (state : At initial coverage old ra s) :
    s.regs.rsp.toBitVec-8 = slot initial 11 := by
  rw [state.stack,UInt64.toBitVec_sub]
  change (initial.data.regs.rsp.toBitVec-80)-8=initial.data.regs.rsp.toBitVec-88
  rw [BitVec.sub_sub]
  rfl

theorem query_high {initial coverage old ra s} (state : At initial coverage old ra s) :
    s.regs.rsp.toBitVec+16 = slot initial 8 := by
  rw [state.stack,UInt64.toBitVec_sub]
  change initial.data.regs.rsp.toBitVec-80+16=initial.data.regs.rsp.toBitVec-64
  rw [show (80 : BitVec 64)=64+16 from rfl,←BitVec.sub_sub,BitVec.sub_add_cancel]

theorem query_low {initial coverage old ra s} (state : At initial coverage old ra s) :
    s.regs.rsp.toBitVec+24 = slot initial 7 := by
  rw [state.stack,UInt64.toBitVec_sub]
  change initial.data.regs.rsp.toBitVec-80+24=initial.data.regs.rsp.toBitVec-56
  rw [show (80 : BitVec 64)=56+24 from rfl,←BitVec.sub_sub,BitVec.sub_add_cancel]

theorem input_frame {c coverage old ra initial world v memory}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (frame : EqualOutside (Writes initial coverage old) initial.data.dmem memory) :
    Allowedips.NetworkKey memory initial.data.regs.rdx.toBitVec c.bits c.key := by
  have same (base : BitVec 64) (width : Nat)
      (subset : ∀ a, InRange base width a → Allowedips.NetworkReads initial.data.regs.rdx.toBitVec c.bits a) :
      initial.data.dmem.loadInt base width = memory.loadInt base width := by
    apply frame.loadInt
    intro i hi written
    have read := subset _ ⟨i,hi,rfl⟩
    rcases written with stack | buffer
    · exact pre.stackInput _ read stack
    · exact pre.bufferInput _ read buffer
  have input := pre.input
  unfold Allowedips.NetworkKey at input ⊢
  by_cases family : c.bits=32
  all_goals simp only [family,↓reduceIte] at input ⊢
  · obtain ⟨word,read,value⟩ := input
    exact ⟨word,(same _ 4 (by intro a h; simpa only [Allowedips.NetworkReads,family,↓reduceIte] using h)).symm.trans read,value⟩
  · obtain ⟨high,low,readHigh,readLow,value⟩ := input
    refine ⟨high,low,?_,?_,value⟩
    · exact (same _ 8 (by
        rintro a ⟨i,hi,eq⟩
        exact ⟨i,by simpa only [Allowedips.NetworkReads,family,↓reduceIte] using (show i<16 by omega),eq⟩)).symm.trans readHigh
    · exact (same _ 8 (by
        rintro a ⟨i,hi,eq⟩
        change InRange _ (if c.bits=32 then 4 else 16) a
        rw [ite_eq_right family]
        exact ⟨8+i,by omega,by simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using eq⟩)).symm.trans readLow

theorem At.family {c coverage old ra initial world v s}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (state : At initial coverage old ra s) :
    s.regs.get (.low .rbx .W8) = .ofNat 8 c.bits ∧
    s.regs.get (.low .r12 .W8) = .ofNat 8 c.bits := by
  have low (r : UInt64) :
      ((r.toBitVec.extractLsb' 0 32).setWidth 64).extractLsb' 0 8 = r.toBitVec.extractLsb' 0 8 := by
    rw [BitVec.extractLsb'_setWidth_of_le (by decide),BitVec.extractLsb'_extractLsb'_of_le (by decide)]
  simpa only [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,Width.bits,Nat.sub_zero,BitVec.extractLsb'_eq_self,
    state.bx,state.r12,UInt64.toBitVec_ofBitVec,low] using And.intro pre.bits pre.bits

#print axioms input_frame
#print axioms At.family
end Binary.AllowedipsEntry
