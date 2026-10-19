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

def cmpCountStores (s : MachineData) (count : BitVec 64) : List WordWrite :=
  let ending := 8#64*(4#64*count)+40#64
  if (8#64*s.regs.rdx.toBitVec).toNat<ending.toNat then [] else
    [⟨s.regs.rax.toBitVec,count+1#64⟩,
     ⟨s.regs.rax.toBitVec+ending-32#64,s.regs.r8.toBitVec⟩,
     ⟨s.regs.rax.toBitVec+ending-24#64,s.regs.r9.toBitVec⟩,
     ⟨s.regs.rax.toBitVec+ending-16#64,s.regs.r10.toBitVec⟩,
     ⟨s.regs.rax.toBitVec+ending-8#64,s.regs.rcx.toBitVec⟩]

theorem cmp_count {rsp : UInt64} (s : MachineData) (ra : UInt64) (count : BitVec 64)
    (read : s.dmem.loadInt s.regs.rax.toBitVec 8=some (count.toNat : Int))
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp (cmpCountStores s count))
    (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra (cmpCountStores s count)) ⟨s,.ofNat 0xffffffff810f3dfc⟩ := by
  subst rsp
  have shift3 (x : BitVec 64) : x <<< 3=x*8#64 := BitVec.shiftLeft_eq_mul_twoPow x 3
  callback_step
  simp [BitVec.signed,read,Effects.All]
  callback_step
  simp [ShiftCountExpr.interpMasked,ShiftCountExpr.interp,ConstExpr.interp,
    BitVec.take,Effects.All,-Bool.forall_bool]
  intro af of
  callback_step
  callback_step
  callback_step
  callback_step
  simp [BitVec.signed,BitVec.ofInt_add,BitVec.ofInt_mul,StatusFlags.from_result,CondCode.interp,
    no_borrow_iff,shift3,BitVec.mul_comm count (4#64),
    BitVec.mul_comm s.regs.rdx.toBitVec (8#64),BitVec.mul_comm (4#64*count) (8#64),
    -BitVec.toNat_add,-BitVec.toNat_mul,-BitVec.toInt_add,-BitVec.toInt_mul]
  by_cases full : (8#64*s.regs.rdx.toBitVec).toNat<(8#64*(4#64*count)+40#64).toNat
  · simp only [full,ite_true,Effects.All]
    have destination : label "L_ffffffff810f3dd9"=.ofNat 0xffffffff810f3dd9 := by decide +kernel
    rw [destination]
    apply leaf_return _ 1 _ ra (by rfl) (by decide) (by rfl) (by rfl) (by exact ret)
    simp [StoresPost,Returned,cmpCountStores,full,Kcov.storesMemory,-BitVec.toNat_add,-BitVec.toNat_mul]
  · simp only [full,ite_false,Effects.All]
    simp only [cmpCountStores,ite_eq_right full] at ready ⊢
    callback_step
    refine eventually_weaken _ _ _ _ ?_ (cmp_store _ ra ?_ ?_ (by rfl))
    · intro t result
      simpa [StoresPost,Returned,cmpStores,BitVec.mul_comm,
        BitVec.add_comm (1#64) count,BitVec.mul_assoc,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        -BitVec.toNat_add,-BitVec.toNat_mul] using result
    · exact ret
    · simpa [cmpStores,BitVec.mul_comm,BitVec.add_comm (1#64) count,
        BitVec.mul_assoc,BitVec.sub_eq_add_neg,BitVec.add_assoc,
        -BitVec.toNat_add,-BitVec.toNat_mul] using ready

def cmpActivePlan (m : Mem 64) (task returnPC tag arg1 arg2 : BitVec 64) : Option (List WordWrite) := do
  let area ← load64 m (task+0x6e8)
  let capacity ← load32 m (task+0x6e4)
  let count ← load64 m area
  let ending := 8#64*(4#64*count)+40#64
  if (8#64*capacity.setWidth 64).toNat<ending.toNat then return []
  return [⟨area,count+1#64⟩,⟨area+ending-32#64,tag⟩,
    ⟨area+ending-24#64,arg1⟩,⟨area+ending-16#64,arg2⟩,⟨area+ending-8#64,returnPC⟩]

theorem cmp_active {rsp : UInt64} (s : MachineData) (ra : UInt64) (writes : List WordWrite)
    (plan : cmpActivePlan s.dmem s.regs.rdx.toBitVec s.regs.rcx.toBitVec s.regs.r8.toBitVec s.regs.r9.toBitVec s.regs.r10.toBitVec=some writes)
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp writes) (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra writes) ⟨s,.ofNat 0xffffffff810f3def⟩ := by
  subst rsp
  unfold cmpActivePlan at plan
  obtain ⟨area,areaRead,plan⟩ := Option.bind_eq_some_iff.mp plan
  obtain ⟨capacity,capacityRead,plan⟩ := Option.bind_eq_some_iff.mp plan
  obtain ⟨count,countRead,plan⟩ := Option.bind_eq_some_iff.mp plan
  have areaRaw := callback_load64_raw _ _ _ areaRead
  have capacityRaw := load32_raw _ _ _ capacityRead
  have countRaw := callback_load64_raw _ _ _ countRead
  have planned : writes=if (8#64*capacity.setWidth 64).toNat<(8#64*(4#64*count)+40#64).toNat then [] else
      [⟨area,count+1#64⟩,⟨area+(8#64*(4#64*count)+40#64)-32#64,s.regs.r8.toBitVec⟩,
       ⟨area+(8#64*(4#64*count)+40#64)-24#64,s.regs.r9.toBitVec⟩,
       ⟨area+(8#64*(4#64*count)+40#64)-16#64,s.regs.r10.toBitVec⟩,
       ⟨area+(8#64*(4#64*count)+40#64)-8#64,s.regs.rcx.toBitVec⟩] := by
    by_cases full : (8#64*capacity.setWidth 64).toNat<(8#64*(4#64*count)+40#64).toNat
    all_goals simpa [full,-BitVec.toNat_add,-BitVec.toNat_mul] using plan.symm
  callback_step
  simp [BitVec.signed,BitVec.ofInt_add] at areaRaw ⊢
  rw [areaRaw]
  simp only [Effects.All]
  callback_step
  simp [BitVec.signed,BitVec.ofInt_add] at capacityRaw ⊢
  rw [capacityRaw]
  simp only [Effects.All]
  refine eventually_weaken _ _ _ _ ?_ (cmp_count _ ra count ?_ ?_ ?_ (by rfl))
  · intro t result
    simpa [StoresPost,Returned,cmpCountStores,planned,-BitVec.toNat_add,-BitVec.toNat_mul] using result
  · simpa using countRaw
  · exact ret
  · simpa [cmpCountStores,planned,-BitVec.toNat_add,-BitVec.toNat_mul] using ready

def cmpModePlan (m : Mem 64) (task returnPC tag arg1 arg2 : BitVec 64) : Option (List WordWrite) := do
  let mode ← load32 m (task+0x6e0)
  if mode != 3 then return []
  cmpActivePlan m task returnPC tag arg1 arg2

theorem cmp_mode {rsp : UInt64} (s : MachineData) (ra : UInt64) (writes : List WordWrite)
    (plan : cmpModePlan s.dmem s.regs.rdx.toBitVec s.regs.rcx.toBitVec s.regs.r8.toBitVec s.regs.r9.toBitVec s.regs.r10.toBitVec=some writes)
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp writes) (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra writes) ⟨s,.ofNat 0xffffffff810f3de4⟩ := by
  subst rsp
  unfold cmpModePlan at plan
  obtain ⟨mode,modeRead,plan⟩ := Option.bind_eq_some_iff.mp plan
  have modeRaw := load32_raw _ _ _ modeRead
  callback_step
  simp [BitVec.signed,BitVec.ofInt_add] at modeRaw ⊢
  rw [modeRaw]
  simp only [Effects.All]
  callback_step
  callback_step
  simp [StatusFlags.from_result,CondCode.interp,BitVec.extractLsb'_setWidth_of_le,
    BitVec.sub_eq_iff_eq_add]
  by_cases active : mode=3#32
  · simp [active,Effects.All]
    refine eventually_weaken _ _ _ _ ?_ (cmp_active _ ra writes ?_ ?_ ?_ (by rfl))
    · intro t result
      simpa [StoresPost,Returned] using result
    · simpa [active] using plan
    · exact ret
    · exact ready
  · simp [active,Effects.All]
    have destination : label "L_ffffffff810f3dd9"=.ofNat 0xffffffff810f3dd9 := by decide +kernel
    rw [destination]
    apply leaf_return _ 1 _ ra (by rfl) (by decide) (by rfl) (by rfl) (by exact ret)
    have empty : writes=[] := by simpa [active] using plan.symm
    simp [StoresPost,Returned,empty,Kcov.storesMemory]

def cmpSoftPlan (m : Mem 64) (task returnPC tag arg1 arg2 : BitVec 64) : Option (List WordWrite) := do
  let enabled ← load32 m (task+0x704)
  if enabled == 0 then return []
  cmpModePlan m task returnPC tag arg1 arg2

theorem cmp_soft {rsp : UInt64} (s : MachineData) (ra : UInt64) (writes : List WordWrite)
    (plan : cmpSoftPlan s.dmem s.regs.rdx.toBitVec s.regs.rcx.toBitVec s.regs.r8.toBitVec s.regs.r9.toBitVec s.regs.r10.toBitVec=some writes)
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp writes) (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra writes) ⟨s,.ofNat 0xffffffff810f3dda⟩ := by
  subst rsp
  unfold cmpSoftPlan at plan
  obtain ⟨enabled,enabledRead,plan⟩ := Option.bind_eq_some_iff.mp plan
  have enabledRaw := load32_raw _ _ _ enabledRead
  callback_step
  simp [BitVec.signed,BitVec.ofInt_add] at enabledRaw ⊢
  rw [enabledRaw]
  simp only [Effects.All]
  callback_step
  intro af
  callback_step
  simp [StatusFlags.from_result,CondCode.interp,BitVec.extractLsb'_setWidth_of_le]
  by_cases disabled : enabled=0#32
  · simp [disabled,Effects.All]
    have destination : label "L_ffffffff810f3dd9"=.ofNat 0xffffffff810f3dd9 := by decide +kernel
    rw [destination]
    apply leaf_return _ 1 _ ra (by rfl) (by decide) (by rfl) (by rfl) (by exact ret)
    have empty : writes=[] := by simpa [disabled] using plan.symm
    simp [StoresPost,Returned,empty,Kcov.storesMemory]
  · simp [disabled,Effects.All]
    refine eventually_weaken _ _ _ _ ?_ (cmp_mode _ ra writes ?_ ?_ ?_ (by rfl))
    · intro t result
      simpa [StoresPost,Returned] using result
    · simpa [disabled] using plan
    · exact ret
    · exact ready

def cmpHardPlan (s : MachineData) : Option (List WordWrite) :=
  if s.regs.rax.toBitVec.extractLsb' 0 32 &&& 0xff0000#32=0#32 then
    cmpSoftPlan s.dmem s.regs.rdx.toBitVec s.regs.rcx.toBitVec s.regs.r8.toBitVec s.regs.r9.toBitVec s.regs.r10.toBitVec else some []

theorem cmp_hardirq {rsp : UInt64} (s : MachineData) (ra : UInt64) (writes : List WordWrite)
    (plan : cmpHardPlan s=some writes)
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp writes) (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra writes) ⟨s,.ofNat 0xffffffff810f3dd2⟩ := by
  subst rsp
  callback_step
  intro af
  callback_step
  simp [StatusFlags.from_result,CondCode.interp]
  by_cases clear : s.regs.rax.toBitVec.extractLsb' 0 32 &&& 0xff0000#32=0#32
  · simp [clear,Effects.All]
    have destination : label "L_ffffffff810f3dda"=.ofNat 0xffffffff810f3dda := by decide +kernel
    rw [destination]
    refine eventually_weaken _ _ _ _ ?_ (cmp_soft _ ra writes ?_ ?_ ?_ (by rfl))
    · intro t result
      simpa [StoresPost,Returned] using result
    · simpa [cmpHardPlan,clear] using plan
    · exact ret
    · exact ready
  · simp [clear,Effects.All]
    apply leaf_return _ 1 _ ra (by rfl) (by decide) (by rfl) (by rfl) (by exact ret)
    have empty : writes=[] := by simpa [cmpHardPlan,clear] using plan.symm
    simp [StoresPost,Returned,empty,Kcov.storesMemory]

def cmpInterruptPlan (s : MachineData) : Option (List WordWrite) :=
  if s.regs.rax.toBitVec.extractLsb' 0 32 &&& 0x100#32=0#32 then some []
  else cmpHardPlan s

theorem cmp_interrupt {rsp : UInt64} (s : MachineData) (ra : UInt64) (writes : List WordWrite)
    (plan : cmpInterruptPlan s=some writes)
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp writes) (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra writes) ⟨s,.ofNat 0xffffffff810f3dcd⟩ := by
  subst rsp
  callback_step
  intro af
  callback_step
  simp [StatusFlags.from_result,CondCode.interp,ah_mask]
  by_cases clear : s.regs.rax.toBitVec.extractLsb' 0 32 &&& 0x100#32=0#32
  · simp [clear,Effects.All]
    have destination : label "L_ffffffff810f3dd9"=.ofNat 0xffffffff810f3dd9 := by decide +kernel
    rw [destination]
    apply leaf_return _ 1 _ ra (by rfl) (by decide) (by rfl) (by rfl) (by exact ret)
    have empty : writes=[] := by simpa [cmpInterruptPlan,clear] using plan.symm
    simp [StoresPost,Returned,empty,Kcov.storesMemory]
  · simp [clear,Effects.All]
    refine eventually_weaken _ _ _ _ ?_ (cmp_hardirq _ ra writes ?_ ?_ ?_ (by rfl))
    · intro t result
      simpa [StoresPost,Returned] using result
    · simpa [cmpHardPlan,cmpInterruptPlan,clear] using plan
    · exact ret
    · exact ready

def cmpGatePlan (s : MachineData) : Option (List WordWrite) :=
  if s.regs.rax.toBitVec.extractLsb' 0 32 &&& 0xff0100#32=0#32 then
    cmpModePlan s.dmem s.regs.rdx.toBitVec s.regs.rcx.toBitVec s.regs.r8.toBitVec s.regs.r9.toBitVec s.regs.r10.toBitVec else cmpInterruptPlan s

theorem cmp_gate {rsp : UInt64} (s : MachineData) (ra : UInt64) (writes : List WordWrite)
    (plan : cmpGatePlan s=some writes)
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp writes) (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra writes) ⟨s,.ofNat 0xffffffff810f3dc6⟩ := by
  subst rsp
  callback_step
  intro af
  callback_step
  simp [StatusFlags.from_result,CondCode.interp]
  by_cases clear : s.regs.rax.toBitVec.extractLsb' 0 32 &&& 0xff0100#32=0#32
  · simp [clear,Effects.All]
    have destination : label "L_ffffffff810f3de4"=.ofNat 0xffffffff810f3de4 := by decide +kernel
    rw [destination]
    refine eventually_weaken _ _ _ _ ?_ (cmp_mode _ ra writes ?_ ?_ ?_ (by rfl))
    · intro t result
      simpa [StoresPost,Returned] using result
    · simpa [cmpGatePlan,clear] using plan
    · exact ret
    · exact ready
  · simp [clear,Effects.All]
    refine eventually_weaken _ _ _ _ ?_ (cmp_interrupt _ ra writes ?_ ?_ ?_ (by rfl))
    · intro t result
      simpa [StoresPost,Returned] using result
    · simpa [cmpGatePlan,cmpInterruptPlan,cmpHardPlan,clear] using plan
    · exact ret
    · exact ready


/-- Common body plan; wrapper arguments have already been widened and tagged. -/
def cmpPlan (s : MachineData) : Option (List WordWrite) := do
  let preempt ← load32 s.dmem preemptCountAddress
  let task ← load64 s.dmem currentTaskAddress
  if preempt &&& 0xff0100 != 0 then
    if preempt &&& 0x100 == 0 || preempt &&& 0xff0000 != 0 then return []
    let enabled ← load32 s.dmem (task+0x704)
    if enabled == 0 then return []
  cmpModePlan s.dmem task s.regs.rcx.toBitVec s.regs.rdi.toBitVec s.regs.rsi.toBitVec s.regs.rdx.toBitVec

/-- One proof of write_comp_data, used by all three index comparison wrappers. -/
theorem cmp_run {rsp : UInt64} (s : MachineData) (ra : UInt64) (writes : List WordWrite)
    (plan : cmpPlan s=some writes)
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp writes) (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra writes) ⟨s,.ofNat 0xffffffff810f3db0⟩ := by
  subst rsp
  unfold cmpPlan at plan
  obtain ⟨preempt,preemptRead,plan⟩ := Option.bind_eq_some_iff.mp plan
  obtain ⟨task,taskRead,plan⟩ := Option.bind_eq_some_iff.mp plan
  have preemptRaw := load32_raw _ _ _ preemptRead
  have taskRaw := callback_load64_raw _ _ _ taskRead
  callback_step
  simp [preemptCountAddress] at preemptRaw ⊢
  rw [preemptRaw]
  simp only [Effects.All]
  callback_step
  callback_step
  callback_step
  callback_step
  simp [currentTaskAddress] at taskRaw ⊢
  rw [taskRaw]
  simp only [Effects.All]
  refine eventually_weaken _ _ _ _ ?_ (cmp_gate _ ra writes ?_ ?_ ?_ (by rfl))
  · intro t result
    simpa [StoresPost,Returned] using result
  · simp [cmpGatePlan,cmpInterruptPlan,cmpHardPlan,cmpSoftPlan,
      BitVec.extractLsb'_setWidth_of_le]
    by_cases h0 : preempt &&& 0xff0100#32=0#32
    all_goals by_cases h1 : preempt &&& 0x100#32=0#32
    all_goals by_cases h2 : preempt &&& 0xff0000#32=0#32
    all_goals simpa [h0,h1,h2] using plan
  · exact ret
  · exact ready

#print axioms cmp_run
end Binary.Callback
