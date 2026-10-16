import AllowedipsEntrySlots
namespace Binary.AllowedipsEntry
open TrustBase CommonBitsCoverage
set_option maxRecDepth 16384

/-- Physical words retained across entry's callbacks and query conversion. -/
structure MemoryAt (initial : MachineState) (coverage : KcovLayout) (old : BitVec 32)
    (ra : UInt64) (memory : Mem 64) : Prop where
  saved : ∀ i<7, memory.loadInt (Allowedips.entrySlot initial.data i) 8 =
    some (((Allowedips.entryWords initial.data)[i]?.getD 0).toNat : Int)
  returnWord : memory.loadInt initial.data.regs.rsp.toBitVec 8 = some ra.toNat
  mapped : ∀ i<18, (memory.loadInt (slot initial (i+1)) 8).isSome = true
  before : AllowedipsCoverageAt coverage old memory
  during : AllowedipsCoverageAt coverage (old+512) memory
  preempt : load32 memory preemptCountAddress = some old

theorem prologue_window (s : MachineState) :
    s.data.regs.rsp.toBitVec-88 = s.data.regs.rsp.toBitVec-144+56 := by
  rw [show (144 : BitVec 64) = 88+56 from rfl, ←BitVec.sub_sub, BitVec.sub_add_cancel]

theorem prologue_inside (s : MachineState) (a : BitVec 64)
    (inside : InRange (s.data.regs.rsp.toBitVec-88) 88 a) : AllowedipsStackWrites s a := by
  obtain ⟨i,hi,eq⟩ := inside
  rw [prologue_window] at eq
  exact ⟨56+i,by omega,by simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using eq⟩

theorem return_prologue_apart (s : MachineState) (a : BitVec 64)
    (inside : InRange s.data.regs.rsp.toBitVec 8 a) :
    ¬InRange (s.data.regs.rsp.toBitVec-88) 88 a := by
  have atSlot : InRange (slot s 0) 8 a := by simpa only [slot, Nat.zero_mul, BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using inside
  rw [slot_window s 0 (by decide)] at atSlot
  rw [prologue_window]
  exact InRange.offset_disjoint _ 144 8 56 88 (by decide) (by decide) (by decide) a atSlot

theorem memory_prologue {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v) :
    MemoryAt initial coverage old ra (Allowedips.entryMemory initial.data 7) := by
  have frame := Allowedips.entryMemory_frame initial.data 7 (by decide)
  have oldState : (Context.mk coverage old).At initial.data.dmem := ⟨pre.coverageBefore,pre.preemptField⟩
  have before := state_frame ⟨coverage,old⟩ _ _ oldState _ frame (by
    intro a member written
    exact pre.stackServices a (AllowedipsCoverage.bytes_before coverage old a member)
      (prologue_inside initial a written))
  have during := coverage_frame ⟨coverage,old+512⟩ _ _ pre.coverageDuring _ frame (by
    intro a member written
    exact pre.stackServices a (AllowedipsCoverage.bytes_during coverage old a member)
      (prologue_inside initial a written))
  refine ⟨?_,?_,?_,before.1,during,before.2⟩
  · intro i hi
    exact Allowedips.entryMemory_read initial.data 7 i (by decide) hi
  · exact (frame.loadInt _ 8 (fun i hi => return_prologue_apart initial _ ⟨i,hi,rfl⟩)).symm.trans pre.entry.2
  · intro i hi
    exact Allowedips.entryMemory_mapped initial.data 7 _ (pre.stack i hi)

/-- The callback's extra CALL store cannot overlap metadata or buffer bytes;
the service's real buffer effect supplies the other phase when active. -/
theorem other_callback_phase {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v) (before after : Mem 64)
    (oldPhase : AllowedipsCoverageAt coverage (old+512) before)
    (newPhase : AllowedipsCoverageAt coverage old after)
    (frame : EqualOutside (fun a => InRange (slot initial 11) 8 a ∨
      (Context.mk coverage old).writes a) before after) :
    AllowedipsCoverageAt coverage (old+512) after := by
  apply coverage_metadata_frame ⟨coverage,old+512⟩ before after oldPhase _ frame
  · intro a read written
    rcases written with stack | buffer
    · exact pre.stackServices a (.inl (.inl (AllowedipsCoverage.metadata_during coverage old a read)))
        (slot_writes initial 11 (by decide) (by decide) a stack)
    · exact pre.bufferMetadata a ⟨.inl buffer.1,buffer.2⟩
        (AllowedipsCoverage.metadata_during coverage old a read)
  · intro needed
    by_cases active : AllowedipsCoverageNeeded coverage old
    · exact (newPhase.2.2.2 active).2.2
    · apply Kcov.buffer_frame coverage before after (oldPhase.2.2.2 needed).2.2 _ frame
      intro a stored written
      rcases written with stack | buffer
      · exact pre.stackServices a (.inl (.inr ⟨.inr needed,stored⟩))
          (slot_writes initial 11 (by decide) (by decide) a stack)
      · exact active buffer.1

/-- Callback writes preserve every live saved word, and the actual returned
call readiness provides the one mapped word which the CALL overwrites. -/
theorem memory_callback {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (before after : Mem 64) (mem : MemoryAt initial coverage old ra before)
    (state : (Context.mk coverage old).At after)
    (mapped : (after.loadInt (slot initial 11) 8).isSome = true)
    (frame : EqualOutside (fun a => InRange (slot initial 11) 8 a ∨
      (Context.mk coverage old).writes a) before after) :
    MemoryAt initial coverage old ra after := by
  have retain (n : Nat) (bound : n ≤ 18) (different : n ≠ 11) :
      before.loadInt (slot initial n) 8 = after.loadInt (slot initial n) 8 := by
    apply frame.loadInt
    intro i hi written
    rcases written with stack | buffer
    · exact slot_apart initial n 11 bound (by decide) different _ ⟨i,hi,rfl⟩ stack
    · exact pre.bufferStack _ ⟨.inl buffer.1,buffer.2⟩
        (slot_live initial n bound _ ⟨i,hi,rfl⟩)
  refine ⟨?_,?_,?_,state.1,other_callback_phase pre before after mem.during state.1 frame,state.2⟩
  · intro i hi
    rw [saved_slot initial i hi]
    rw [←retain _ (by split <;> omega) (by split <;> omega)]
    rw [←saved_slot initial i hi]
    exact mem.saved i hi
  · have eq := retain 0 (by decide) (by decide)
    simp only [slot, Nat.zero_mul, BitVec.ofNat_eq_ofNat, BitVec.sub_zero] at eq
    exact eq.symm.trans mem.returnWord
  · intro i hi
    by_cases equal : i+1=11
    · simpa only [equal] using mapped
    · rw [←retain (i+1) (by omega) equal]
      exact mem.mapped i hi

/-- The query occupies precisely the two local words at entry RSP minus 64 and minus 56;
its real stores preserve saves, return word, and callback state. -/
theorem memory_query_store {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (memory : Mem 64) (mem : MemoryAt initial coverage old ra memory)
    (n width : Nat) (query : n=7 ∨ n=8) (widthBound : width≤8) (value : Int) :
    MemoryAt initial coverage old ra (memory.storeInt (slot initial n) width value) := by
  have bound : n≤18 := by rcases query with rfl | rfl <;> decide
  have lower : 1≤n := by rcases query with rfl | rfl <;> decide
  have subset (a : BitVec 64) (inside : InRange (slot initial n) width a) :
      InRange (slot initial n) 8 a := by
    obtain ⟨i,hi,eq⟩ := inside
    exact ⟨i,by omega,eq⟩
  have frame := storeInt_frame memory (slot initial n) width value
  have retain (j : Nat) (jb : j≤18) (different : j≠n) :
      memory.loadInt (slot initial j) 8 =
      (memory.storeInt (slot initial n) width value).loadInt (slot initial j) 8 := by
    apply frame.loadInt
    intro i hi written
    exact slot_apart initial j n jb bound different _ ⟨i,hi,rfl⟩ (subset _ written)
  have before := state_frame ⟨coverage,old⟩ _ _ ⟨mem.before,mem.preempt⟩ _ frame (by
    intro a member written
    exact pre.stackServices a (AllowedipsCoverage.bytes_before coverage old a member)
      (slot_writes initial n lower bound a (subset a written)))
  have during := coverage_frame ⟨coverage,old+512⟩ _ _ mem.during _ frame (by
    intro a member written
    exact pre.stackServices a (AllowedipsCoverage.bytes_during coverage old a member)
      (slot_writes initial n lower bound a (subset a written)))
  refine ⟨?_,?_,?_,before.1,during,before.2⟩
  · intro i hi
    rw [saved_slot initial i hi]
    have different : (if i<6 then i+1 else 9) ≠ n := by
      rcases query with rfl | rfl <;> split <;> omega
    rw [←retain _ (by split <;> omega) different,←saved_slot initial i hi]
    exact mem.saved i hi
  · have eq := retain 0 (by decide) (by omega)
    simp only [slot, Nat.zero_mul, BitVec.ofNat_eq_ofNat, BitVec.sub_zero] at eq
    exact eq.symm.trans mem.returnWord
  · intro i hi
    exact storeInt_defined memory (slot initial (i+1)) (slot initial n) 8 width value (mem.mapped i hi)

theorem memory_ready {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v) (s : MachineData)
    (mem : MemoryAt initial coverage old ra s.dmem)
    (stack : s.regs.rsp = initial.data.regs.rsp-80) : CallsReady ⟨coverage,old⟩ s := by
  have push : s.regs.rsp.toBitVec-8 = slot initial 11 := by
    rw [stack,UInt64.toBitVec_sub]
    change (initial.data.regs.rsp.toBitVec-80)-8 = initial.data.regs.rsp.toBitVec-88
    rw [BitVec.sub_sub]
    rfl
  refine ⟨⟨mem.before,mem.preempt⟩,?_,?_,?_,?_,?_,?_⟩
  · rw [stack]
    simp only [UInt64.toNat_sub,show (80 : UInt64).toNat = 80 from rfl]
    have aligned := pre.entry.1
    have bound := initial.data.regs.rsp.toNat_lt_size
    omega
  · rw [push]
    exact mem.mapped 10 (by decide)
  · intro a member inside
    rw [push] at inside
    exact pre.stackServices a (AllowedipsCoverage.bytes_before coverage old a member)
      (slot_writes initial 11 (by decide) (by decide) a inside)
  · intro a written inside
    rw [push] at inside
    exact pre.bufferStack a ⟨.inl written.1,written.2⟩ (slot_live initial 11 (by decide) a inside)
  · intro a written metadata
    exact pre.bufferMetadata a ⟨.inl written.1,written.2⟩ (AllowedipsCoverage.metadata_before coverage old a metadata)
  · intro a written inside
    exact pre.bufferPreempt a ⟨.inl written.1,written.2⟩ inside

#print axioms memory_ready
#print axioms memory_query_store
#print axioms memory_callback
#print axioms memory_prologue
#print axioms other_callback_phase
end Binary.AllowedipsEntry
