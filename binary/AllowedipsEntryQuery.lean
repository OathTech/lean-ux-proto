import AllowedipsEntryState
import AllowedipsEntryRegionTrace

namespace Binary.AllowedipsEntry
open TrustBase CommonBitsCoverage CommonBits
local instance : Labels := Image.linkedLabels

/-- The two query slots are inside the write footprint, independently of
modular wraparound of the stack pointer. -/
theorem query_subset {initial coverage old ra s} (state : At initial coverage old ra s)
    (a : BitVec 64) (inside : InRange (s.regs.rsp.toBitVec+16) 8 a ∨
      InRange (s.regs.rsp.toBitVec+24) 8 a) : Writes initial coverage old a := by
  rcases inside with high | low
  · rw [query_high state] at high
    exact .inl (slot_writes initial 8 (by decide) (by decide) a high)
  · rw [query_low state] at low
    exact .inl (slot_writes initial 7 (by decide) (by decide) a low)

theorem At.advance {initial coverage old ra before after}
    (state : At initial coverage old ra before)
    (memory : MemoryAt initial coverage old ra after.dmem)
    (stack : after.regs.rsp=before.regs.rsp) (bx : after.regs.rbx=before.regs.rbx)
    (bp : after.regs.rbp=before.regs.rbp) (r12 : after.regs.r12=before.regs.r12)
    (frame : EqualOutside (Writes initial coverage old) before.dmem after.dmem) :
    At initial coverage old ra after :=
  ⟨stack.trans state.stack,bx.trans state.bx,bp.trans state.bp,r12.trans state.r12,memory,
   fun a outside => (state.frame a outside).trans (frame a outside)⟩

theorem initialize_query (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (s : MachineData) (state : At initial coverage old ra s) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc=AllowedipsImage.Lookup.entry+0x39 ∧ At initial coverage old ra t.machine.data) ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+0x20⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x20⟩,[⟨s,AllowedipsImage.Lookup.entry+0x20⟩]⟩ := by
  have mappedHigh : (s.dmem.loadInt (s.regs.rsp.toBitVec+16) 8).isSome = true := by
    rw [query_high state]; exact state.memory.mapped 7 (by decide)
  have mappedLow : ((Allowedips.zeroHigh s).loadInt (s.regs.rsp.toBitVec+24) 8).isSome = true := by
    apply storeInt_defined
    rw [query_low state]; exact state.memory.mapped 6 (by decide)
  obtain ⟨high,highRead⟩ := Option.isSome_iff_exists.mp mappedHigh
  obtain ⟨low,lowRead⟩ := Option.isSome_iff_exists.mp mappedLow
  have run := initialize_trace fetch agree s high low highRead lowRead rxSection
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨⟨regs,memory,pc⟩,trace⟩
  have localTrace := trace.mono (query_subset state)
  refine ⟨⟨pc,state.advance ?_ (by simp only [regs]) (by simp only [regs])
    (by simp only [regs]) (by simp only [regs]) localTrace.frame⟩,localTrace⟩
  rw [memory,Allowedips.zeroHigh,query_high state,query_low state]
  exact memory_query_store pre _
    (memory_query_store pre _ state.memory 8 8 (.inr rfl) (by decide) 0)
    7 8 (.inl rfl) (by decide) 0

theorem endian32 (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v) (family : c.bits=32)
    (s : MachineData) (state : At initial coverage old ra s) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc=AllowedipsImage.Lookup.entry+0x61 ∧ At initial coverage old ra t.machine.data ∧
       AllowedipsChild.QueryWords t.machine.data.dmem (slot initial 8) c.bits c.key) ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+0x176⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x176⟩,[⟨s,AllowedipsImage.Lookup.entry+0x176⟩]⟩ := by
  have input := input_frame pre state.frame
  simp only [Allowedips.NetworkKey,family,↓reduceIte] at input
  obtain ⟨network,read,value⟩ := input
  have mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec+16) 4).isSome = true := by
    rw [query_high state,loadInt_defined]
    have full := (loadInt_defined _ _ _).mp (state.memory.mapped 7 (by decide))
    intro i hi; exact full i (by omega)
  obtain ⟨word,mapped⟩ := Option.isSome_iff_exists.mp mapped
  have run := endian32_trace fetch agree s network word (by rw [state.bp]; exact read) mapped rxSection
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨⟨regs,memory,pc⟩,trace⟩
  have localTrace := trace.mono (fun a ⟨i,hi,eq⟩ => query_subset state a (.inl ⟨i,by omega,eq⟩))
  refine ⟨⟨pc,state.advance ?_ (by simp only [regs]) (by simp only [regs])
    (by simp only [regs]) (by simp only [regs]) localTrace.frame,?_⟩,localTrace⟩
  · rw [memory,query_high state]
    exact memory_query_store pre _ state.memory 8 4 (.inr rfl) (by decide) _
  · simp only [AllowedipsChild.QueryWords,family,↓reduceIte,memory,query_high state]
    rw [←value]
    exact load32_store _ _ _

theorem endian128 (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v) (family : c.bits=128)
    (s : MachineData) (state : At initial coverage old ra s) (rxSection : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc=AllowedipsImage.Lookup.entry+0x61 ∧ At initial coverage old ra t.machine.data ∧
       AllowedipsChild.QueryWords t.machine.data.dmem (slot initial 8) c.bits c.key) ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+0x154⟩ rxSection [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x154⟩,[⟨s,AllowedipsImage.Lookup.entry+0x154⟩]⟩ := by
  have input := input_frame pre state.frame
  simp only [Allowedips.NetworkKey,family,show ¬(128=32) by decide,↓reduceIte] at input
  obtain ⟨high,low,highRead,lowRead,value⟩ := input
  have highFrame : EqualOutside (Writes initial coverage old) s.dmem (Allowedips.highStored s high) := by
    intro a outside
    apply storeInt_frame _ _ _ _ a
    intro written
    exact outside (query_subset state a (.inl written))
  have combined : EqualOutside (Writes initial coverage old) initial.data.dmem (Allowedips.highStored s high) :=
    fun a outside => (state.frame a outside).trans (highFrame a outside)
  have lowRead' : (Allowedips.highStored s high).loadInt (s.regs.rbp.toBitVec+8) 8 = some low.toNat := by
    rw [state.bp]
    have same := highFrame.loadInt (initial.data.regs.rdx.toBitVec+8) 8 (by
      intro i hi written
      have inputByte : Allowedips.NetworkReads initial.data.regs.rdx.toBitVec c.bits
          (initial.data.regs.rdx.toBitVec+8+.ofNat 64 i) := by
        rw [Allowedips.NetworkReads,family]
        change InRange _ 16 _
        exact ⟨8+i,by omega,by simp only [BitVec.ofNat_add,BitVec.add_assoc]; rfl⟩
      rcases written with stack | buffer
      · exact pre.stackInput _ inputByte stack
      · exact pre.bufferInput _ inputByte buffer)
    exact same.symm.trans lowRead
  have highMapped : (s.dmem.loadInt (s.regs.rsp.toBitVec+16) 8).isSome = true := by
    rw [query_high state]; exact state.memory.mapped 7 (by decide)
  have lowMapped : ((Allowedips.highStored s high).loadInt (s.regs.rsp.toBitVec+24) 8).isSome = true := by
    apply storeInt_defined
    rw [query_low state]; exact state.memory.mapped 6 (by decide)
  obtain ⟨highOld,highMapped⟩ := Option.isSome_iff_exists.mp highMapped
  obtain ⟨lowOld,lowMapped⟩ := Option.isSome_iff_exists.mp lowMapped
  have run := endian128_trace fetch agree s high low highOld lowOld
    (by rw [state.bp]; exact highRead) highMapped lowRead' lowMapped rxSection
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨⟨regs,memory,pc⟩,trace⟩
  have localTrace := trace.mono (query_subset state)
  refine ⟨⟨pc,state.advance ?_ (by simp only [regs]) (by simp only [regs])
    (by simp only [regs]) (by simp only [regs]) localTrace.frame,?_⟩,localTrace⟩
  · rw [memory,Allowedips.highStored,query_high state,query_low state]
    exact memory_query_store pre _
      (memory_query_store pre _ state.memory 8 8 (.inr rfl) (by decide) _)
      7 8 (.inl rfl) (by decide) _
  · have highBound := (Allowedips.swap64 high).isLt
    have lowBound := (Allowedips.swap64 low).isLt
    have div : c.key/2^64=(Allowedips.swap64 high).toNat := by rw [←value]; omega
    have mod : c.key%2^64=(Allowedips.swap64 low).toNat := by rw [←value]; omega
    have lowSlot : slot initial 8+8=slot initial 7 := by
      unfold slot
      change initial.data.regs.rsp.toBitVec-64+8=initial.data.regs.rsp.toBitVec-56
      rw [show (64 : BitVec 64)=56+8 from rfl,←BitVec.sub_sub,BitVec.sub_add_cancel]
    simp only [AllowedipsChild.QueryWords,family,show ¬(128=32) by decide,↓reduceIte,
      div,mod,memory,Allowedips.highStored,query_high state,query_low state,lowSlot]
    constructor
    · have retain := (storeInt_frame (s.dmem.storeInt (slot initial 8) 8 (Allowedips.swap64 high).toInt)
        (slot initial 7) 8 (Allowedips.swap64 low).toInt).loadInt (slot initial 8) 8
        (fun i hi => slot_apart initial 8 7 (by decide) (by decide) (by decide) _ ⟨i,hi,rfl⟩)
      exact retain.symm.trans (load64_store _ _ _)
    · exact load64_store _ _ _

#print axioms initialize_query
#print axioms endian32
#print axioms endian128
end Binary.AllowedipsEntry
