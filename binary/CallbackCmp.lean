import CallbackKcovMemory

namespace Binary.Callback
open TrustBase
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def cmpStores (s : MachineData) : List WordWrite :=
  [⟨s.regs.rax.toBitVec,s.regs.rdi.toBitVec⟩,
   ⟨s.regs.rax.toBitVec+s.regs.rsi.toBitVec-32#64,s.regs.r8.toBitVec⟩,
   ⟨s.regs.rax.toBitVec+s.regs.rsi.toBitVec-24#64,s.regs.r9.toBitVec⟩,
   ⟨s.regs.rax.toBitVec+s.regs.rsi.toBitVec-16#64,s.regs.r10.toBitVec⟩,
   ⟨s.regs.rax.toBitVec+s.regs.r11.toBitVec*8#64+32#64,s.regs.rcx.toBitVec⟩]

theorem cmp_store {rsp : UInt64} (s : MachineData) (ra : UInt64)
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp (cmpStores s)) (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra (cmpStores s)) ⟨s,.ofNat 0xffffffff810f3e1c⟩ := by
  subst rsp
  have kept := stores_return s ra (cmpStores s) ready ret
  have mapped0 := Kcov.stores_mapped [] s.dmem
    (s.regs.rax.toBitVec) 8 (ready ⟨s.regs.rax.toBitVec,s.regs.rdi.toBitVec⟩ (by simp [cmpStores])).1
  obtain ⟨old0,read0⟩ := Option.isSome_iff_exists.mp mapped0
  simp only [Kcov.storesMemory,List.foldl_nil] at read0
  have mapped1 := Kcov.stores_mapped [⟨s.regs.rax.toBitVec,s.regs.rdi.toBitVec⟩] s.dmem
    (s.regs.rax.toBitVec+s.regs.rsi.toBitVec-32#64) 8 (ready ⟨s.regs.rax.toBitVec+s.regs.rsi.toBitVec-32#64,s.regs.r8.toBitVec⟩ (by simp [cmpStores])).1
  obtain ⟨old1,read1⟩ := Option.isSome_iff_exists.mp mapped1
  simp only [Kcov.storesMemory,List.foldl_cons,List.foldl_nil] at read1
  have mapped2 := Kcov.stores_mapped [⟨s.regs.rax.toBitVec,s.regs.rdi.toBitVec⟩,⟨s.regs.rax.toBitVec+s.regs.rsi.toBitVec-32#64,s.regs.r8.toBitVec⟩] s.dmem
    (s.regs.rax.toBitVec+s.regs.rsi.toBitVec-24#64) 8 (ready ⟨s.regs.rax.toBitVec+s.regs.rsi.toBitVec-24#64,s.regs.r9.toBitVec⟩ (by simp [cmpStores])).1
  obtain ⟨old2,read2⟩ := Option.isSome_iff_exists.mp mapped2
  simp only [Kcov.storesMemory,List.foldl_cons,List.foldl_nil] at read2
  have mapped3 := Kcov.stores_mapped [⟨s.regs.rax.toBitVec,s.regs.rdi.toBitVec⟩,⟨s.regs.rax.toBitVec+s.regs.rsi.toBitVec-32#64,s.regs.r8.toBitVec⟩,⟨s.regs.rax.toBitVec+s.regs.rsi.toBitVec-24#64,s.regs.r9.toBitVec⟩] s.dmem
    (s.regs.rax.toBitVec+s.regs.rsi.toBitVec-16#64) 8 (ready ⟨s.regs.rax.toBitVec+s.regs.rsi.toBitVec-16#64,s.regs.r10.toBitVec⟩ (by simp [cmpStores])).1
  obtain ⟨old3,read3⟩ := Option.isSome_iff_exists.mp mapped3
  simp only [Kcov.storesMemory,List.foldl_cons,List.foldl_nil] at read3
  have mapped4 := Kcov.stores_mapped [⟨s.regs.rax.toBitVec,s.regs.rdi.toBitVec⟩,⟨s.regs.rax.toBitVec+s.regs.rsi.toBitVec-32#64,s.regs.r8.toBitVec⟩,⟨s.regs.rax.toBitVec+s.regs.rsi.toBitVec-24#64,s.regs.r9.toBitVec⟩,⟨s.regs.rax.toBitVec+s.regs.rsi.toBitVec-16#64,s.regs.r10.toBitVec⟩] s.dmem
    (s.regs.rax.toBitVec+s.regs.r11.toBitVec*8#64+32#64) 8 (ready ⟨s.regs.rax.toBitVec+s.regs.r11.toBitVec*8#64+32#64,s.regs.rcx.toBitVec⟩ (by simp [cmpStores])).1
  obtain ⟨old4,read4⟩ := Option.isSome_iff_exists.mp mapped4
  simp only [Kcov.storesMemory,List.foldl_cons,List.foldl_nil] at read4
  callback_step
  simp [BitVec.signed] at read0 ⊢
  rw [read0]
  simp only [Effects.All]
  callback_step
  simp [BitVec.signed,BitVec.ofInt_add,BitVec.sub_eq_add_neg] at read1 ⊢
  rw [read1]
  simp only [Effects.All]
  callback_step
  simp [BitVec.signed,BitVec.ofInt_add,BitVec.sub_eq_add_neg] at read2 ⊢
  rw [read2]
  simp only [Effects.All]
  callback_step
  simp [BitVec.signed,BitVec.ofInt_add,BitVec.sub_eq_add_neg] at read3 ⊢
  rw [read3]
  simp only [Effects.All]
  callback_step
  simp [BitVec.signed,BitVec.ofInt_add,BitVec.ofInt_mul,BitVec.sub_eq_add_neg] at read4 ⊢
  rw [read4]
  simp only [Effects.All]
  apply leaf_return _ 1 _ ra (by rfl) (by decide) (by rfl) (by rfl)
  · simpa [cmpStores,Kcov.storesMemory,BitVec.sub_eq_add_neg] using kept
  · simp [StoresPost,Returned,cmpStores,Kcov.storesMemory,BitVec.sub_eq_add_neg]

end Binary.Callback
