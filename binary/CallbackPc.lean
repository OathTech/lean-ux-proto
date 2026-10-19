import CallbackKcovMemory

namespace Binary.Callback
open TrustBase
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def pcStores (s : MachineData) : List WordWrite :=
  [⟨s.regs.rcx.toBitVec,s.regs.rax.toBitVec⟩,
   ⟨s.regs.rcx.toBitVec+s.regs.rax.toBitVec*8#64,s.regs.rsi.toBitVec⟩]

theorem pc_store {rsp : UInt64} (s : MachineData) (ra : UInt64)
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp (pcStores s))
    (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra (pcStores s)) ⟨s,.ofNat 0xffffffff810f3153⟩ := by
  subst rsp
  have first := (ready ⟨s.regs.rcx.toBitVec,s.regs.rax.toBitVec⟩ (by simp [pcStores])).1
  have second := (ready ⟨s.regs.rcx.toBitVec+s.regs.rax.toBitVec*8#64,s.regs.rsi.toBitVec⟩
    (by simp [pcStores])).1
  have mapped := storeInt_defined s.dmem (s.regs.rcx.toBitVec+s.regs.rax.toBitVec*8#64)
    s.regs.rcx.toBitVec 8 8 s.regs.rax.toBitVec.toInt second
  obtain ⟨firstValue,firstRead⟩ := Option.isSome_iff_exists.mp first
  obtain ⟨secondValue,secondRead⟩ := Option.isSome_iff_exists.mp mapped
  have kept := stores_return s ra (pcStores s) ready ret
  callback_step
  dsimp only at firstRead
  simp [BitVec.signed,firstRead,Effects.All]
  callback_step
  simp [BitVec.signed,BitVec.ofInt_add,BitVec.ofInt_mul,secondRead,Effects.All]
  apply leaf_return _ 1 _ ra (by rfl) (by decide) (by rfl) (by rfl)
  · exact kept
  · simp [StoresPost,Returned,pcStores,Kcov.storesMemory]

def pcCountStores (s : MachineData) (count : BitVec 64) : List WordWrite :=
  if s.regs.rdx.toNat≤(count+1#64).toNat then [] else
    [⟨s.regs.rcx.toBitVec,count+1#64⟩,
     ⟨s.regs.rcx.toBitVec+(count+1#64)*8#64,s.regs.rsi.toBitVec⟩]

theorem pc_count {rsp : UInt64} (s : MachineData) (ra : UInt64) (count : BitVec 64)
    (read : s.dmem.loadInt s.regs.rcx.toBitVec 8=some (count.toNat : Int))
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp (pcCountStores s count))
    (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra (pcCountStores s count)) ⟨s,.ofNat 0xffffffff810f3147⟩ := by
  subst rsp
  callback_step
  simp [BitVec.signed,read,Effects.All]
  callback_step
  callback_step
  callback_step
  simp [StatusFlags.from_result,CondCode.interp,no_borrow_iff,
    BitVec.add_comm (1#64) count,-BitVec.toNat_add]
  by_cases full : s.regs.rdx.toNat≤(count+1#64).toNat
  · simp only [full,ite_true,Effects.All]
    have destination : label "L_ffffffff810f3124"=.ofNat 0xffffffff810f3124 := by decide +kernel
    rw [destination]
    apply leaf_return _ 1 _ ra (by rfl) (by decide) (by rfl) (by rfl) (by exact ret)
    simp [StoresPost,Returned,pcCountStores,full,Kcov.storesMemory,-BitVec.toNat_add]
  · simp only [full,ite_false,Effects.All]
    refine eventually_weaken _ _ _ _ ?_ (pc_store _ ra ?_ ?_ (by rfl))
    · intro t result
      simpa [StoresPost,Returned,pcStores,pcCountStores,full,-BitVec.toNat_add] using result
    · exact ret
    · simpa [pcStores,pcCountStores,full,-BitVec.toNat_add] using ready

def pcActivePlan (m : Mem 64) (task returnPC : BitVec 64) : Option (List WordWrite) := do
  let area ← load64 m (task+0x6e8)
  let capacity ← load32 m (task+0x6e4)
  let count ← load64 m area
  if capacity.toNat≤(count+1#64).toNat then return []
  return [⟨area,count+1#64⟩,⟨area+(count+1#64)*8#64,returnPC⟩]

theorem pc_active {rsp : UInt64} (s : MachineData) (ra : UInt64) (writes : List WordWrite)
    (plan : pcActivePlan s.dmem s.regs.rdx.toBitVec s.regs.rsi.toBitVec=some writes)
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp writes) (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra writes) ⟨s,.ofNat 0xffffffff810f313a⟩ := by
  subst rsp
  unfold pcActivePlan at plan
  obtain ⟨area,areaRead,plan⟩ := Option.bind_eq_some_iff.mp plan
  obtain ⟨capacity,capacityRead,plan⟩ := Option.bind_eq_some_iff.mp plan
  obtain ⟨count,countRead,plan⟩ := Option.bind_eq_some_iff.mp plan
  have areaRaw := callback_load64_raw _ _ _ areaRead
  have capacityRaw := load32_raw _ _ _ capacityRead
  have countRaw := callback_load64_raw _ _ _ countRead
  have capacityWide : capacity.toNat<18446744073709551616 := Nat.lt_trans capacity.isLt (by decide)
  have planned : writes=if capacity.toNat≤(count+1#64).toNat then [] else
      [⟨area,count+1#64⟩,⟨area+(count+1#64)*8#64,s.regs.rsi.toBitVec⟩] := by
    by_cases full : capacity.toNat≤(count+1#64).toNat
    all_goals simpa [full,-BitVec.toNat_add] using plan.symm
  callback_step
  simp [BitVec.signed,BitVec.ofInt_add] at areaRaw ⊢
  rw [areaRaw]
  simp only [Effects.All]
  callback_step
  simp [BitVec.signed,BitVec.ofInt_add] at capacityRaw ⊢
  rw [capacityRaw]
  simp only [Effects.All]
  refine eventually_weaken _ _ _ _ ?_ (pc_count _ ra count ?_ ?_ ?_ (by rfl))
  · intro t result
    simpa [StoresPost,Returned,pcCountStores,planned,Nat.mod_eq_of_lt capacityWide,-BitVec.toNat_add] using result
  · simpa using countRaw
  · exact ret
  · simpa [pcCountStores,planned,Nat.mod_eq_of_lt capacityWide,-BitVec.toNat_add] using ready

def pcModePlan (m : Mem 64) (task returnPC : BitVec 64) : Option (List WordWrite) := do
  let mode ← load32 m (task+0x6e0)
  if mode != 2 then return []
  pcActivePlan m task returnPC

theorem pc_mode {rsp : UInt64} (s : MachineData) (ra : UInt64) (writes : List WordWrite)
    (plan : pcModePlan s.dmem s.regs.rdx.toBitVec s.regs.rsi.toBitVec=some writes)
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp writes) (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra writes) ⟨s,.ofNat 0xffffffff810f312f⟩ := by
  subst rsp
  unfold pcModePlan at plan
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
  by_cases active : mode=2#32
  · simp [active,Effects.All]
    refine eventually_weaken _ _ _ _ ?_ (pc_active _ ra writes ?_ ?_ ?_ (by rfl))
    · intro t result
      simpa [StoresPost,Returned] using result
    · simpa [active] using plan
    · exact ret
    · exact ready
  · simp [active,Effects.All]
    have destination : label "L_ffffffff810f3124"=.ofNat 0xffffffff810f3124 := by decide +kernel
    rw [destination]
    apply leaf_return _ 1 _ ra (by rfl) (by decide) (by rfl) (by rfl) (by exact ret)
    have empty : writes=[] := by simpa [active] using plan.symm
    simp [StoresPost,Returned,empty,Kcov.storesMemory]

def pcSoftPlan (m : Mem 64) (task returnPC : BitVec 64) : Option (List WordWrite) := do
  let enabled ← load32 m (task+0x704)
  if enabled == 0 then return []
  pcModePlan m task returnPC

theorem pc_soft {rsp : UInt64} (s : MachineData) (ra : UInt64) (writes : List WordWrite)
    (plan : pcSoftPlan s.dmem s.regs.rdx.toBitVec s.regs.rsi.toBitVec=some writes)
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp writes) (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra writes) ⟨s,.ofNat 0xffffffff810f3125⟩ := by
  subst rsp
  unfold pcSoftPlan at plan
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
    have destination : label "L_ffffffff810f3124"=.ofNat 0xffffffff810f3124 := by decide +kernel
    rw [destination]
    apply leaf_return _ 1 _ ra (by rfl) (by decide) (by rfl) (by rfl) (by exact ret)
    have empty : writes=[] := by simpa [disabled] using plan.symm
    simp [StoresPost,Returned,empty,Kcov.storesMemory]
  · simp [disabled,Effects.All]
    refine eventually_weaken _ _ _ _ ?_ (pc_mode _ ra writes ?_ ?_ ?_ (by rfl))
    · intro t result
      simpa [StoresPost,Returned] using result
    · simpa [disabled] using plan
    · exact ret
    · exact ready

def pcHardPlan (s : MachineData) : Option (List WordWrite) :=
  if s.regs.rax.toBitVec.extractLsb' 0 32 &&& 0xff0000#32=0#32 then
    pcSoftPlan s.dmem s.regs.rdx.toBitVec s.regs.rsi.toBitVec else some []

theorem pc_hardirq {rsp : UInt64} (s : MachineData) (ra : UInt64) (writes : List WordWrite)
    (plan : pcHardPlan s=some writes)
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp writes) (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra writes) ⟨s,.ofNat 0xffffffff810f311d⟩ := by
  subst rsp
  callback_step
  intro af
  callback_step
  simp [StatusFlags.from_result,CondCode.interp]
  by_cases clear : s.regs.rax.toBitVec.extractLsb' 0 32 &&& 0xff0000#32=0#32
  · simp [clear,Effects.All]
    have destination : label "L_ffffffff810f3125"=.ofNat 0xffffffff810f3125 := by decide +kernel
    rw [destination]
    refine eventually_weaken _ _ _ _ ?_ (pc_soft _ ra writes ?_ ?_ ?_ (by rfl))
    · intro t result
      simpa [StoresPost,Returned] using result
    · simpa [pcHardPlan,clear] using plan
    · exact ret
    · exact ready
  · simp [clear,Effects.All]
    apply leaf_return _ 1 _ ra (by rfl) (by decide) (by rfl) (by rfl) (by exact ret)
    have empty : writes=[] := by simpa [pcHardPlan,clear] using plan.symm
    simp [StoresPost,Returned,empty,Kcov.storesMemory]

def pcInterruptPlan (s : MachineData) : Option (List WordWrite) :=
  if s.regs.rax.toBitVec.extractLsb' 0 32 &&& 0x100#32=0#32 then some []
  else pcHardPlan s

theorem pc_interrupt {rsp : UInt64} (s : MachineData) (ra : UInt64) (writes : List WordWrite)
    (plan : pcInterruptPlan s=some writes)
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp writes) (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra writes) ⟨s,.ofNat 0xffffffff810f3118⟩ := by
  subst rsp
  callback_step
  intro af
  callback_step
  simp [StatusFlags.from_result,CondCode.interp,ah_mask]
  by_cases clear : s.regs.rax.toBitVec.extractLsb' 0 32 &&& 0x100#32=0#32
  · simp [clear,Effects.All]
    have destination : label "L_ffffffff810f3124"=.ofNat 0xffffffff810f3124 := by decide +kernel
    rw [destination]
    apply leaf_return _ 1 _ ra (by rfl) (by decide) (by rfl) (by rfl) (by exact ret)
    have empty : writes=[] := by simpa [pcInterruptPlan,clear] using plan.symm
    simp [StoresPost,Returned,empty,Kcov.storesMemory]
  · simp [clear,Effects.All]
    refine eventually_weaken _ _ _ _ ?_ (pc_hardirq _ ra writes ?_ ?_ ?_ (by rfl))
    · intro t result
      simpa [StoresPost,Returned] using result
    · simpa [pcHardPlan,pcInterruptPlan,clear] using plan
    · exact ret
    · exact ready

def pcGatePlan (s : MachineData) : Option (List WordWrite) :=
  if s.regs.rax.toBitVec.extractLsb' 0 32 &&& 0xff0100#32=0#32 then
    pcModePlan s.dmem s.regs.rdx.toBitVec s.regs.rsi.toBitVec else pcInterruptPlan s

theorem pc_gate {rsp : UInt64} (s : MachineData) (ra : UInt64) (writes : List WordWrite)
    (plan : pcGatePlan s=some writes)
    (ret : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int))
    (ready : WritesReady s.dmem s.regs.rsp writes) (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (StoresPost s ra writes) ⟨s,.ofNat 0xffffffff810f3111⟩ := by
  subst rsp
  callback_step
  intro af
  callback_step
  simp [StatusFlags.from_result,CondCode.interp]
  by_cases clear : s.regs.rax.toBitVec.extractLsb' 0 32 &&& 0xff0100#32=0#32
  · simp [clear,Effects.All]
    have destination : label "L_ffffffff810f312f"=.ofNat 0xffffffff810f312f := by decide +kernel
    rw [destination]
    refine eventually_weaken _ _ _ _ ?_ (pc_mode _ ra writes ?_ ?_ ?_ (by rfl))
    · intro t result
      simpa [StoresPost,Returned] using result
    · simpa [pcGatePlan,clear] using plan
    · exact ret
    · exact ready
  · simp [clear,Effects.All]
    refine eventually_weaken _ _ _ _ ?_ (pc_interrupt _ ra writes ?_ ?_ ?_ (by rfl))
    · intro t result
      simpa [StoresPost,Returned] using result
    · simpa [pcGatePlan,pcInterruptPlan,pcHardPlan,clear] using plan
    · exact ret
    · exact ready

theorem pc_run (s : MachineData) (ra : UInt64)
    (ready : KcovReady .pc ⟨s,.ofNat 0xffffffff810f3100⟩)
    (frame : EntryFrame ⟨s,.ofNat 0xffffffff810f3100⟩ ra) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard s.regs.rsp))
      (fun t => Returned ⟨s,.ofNat 0xffffffff810f3100⟩ t ra ∧
        EqualOutside (KcovWrites .pc ⟨s,.ofNat 0xffffffff810f3100⟩) s.dmem t.data.dmem ∧
        KcovEffect .pc ⟨s,.ofNat 0xffffffff810f3100⟩ t)
      ⟨s,.ofNat 0xffffffff810f3100⟩ := by
  obtain ⟨writes,wholePlan,ready⟩ := ready
  have plan := wholePlan
  unfold KcovPlan at plan
  obtain ⟨preempt,preemptRead,plan⟩ := Option.bind_eq_some_iff.mp plan
  obtain ⟨returnPC,returnRead,plan⟩ := Option.bind_eq_some_iff.mp plan
  obtain ⟨task,taskRead,plan⟩ := Option.bind_eq_some_iff.mp plan
  have preemptRaw := load32_raw _ _ _ preemptRead
  have returnRaw := callback_load64_raw _ _ _ returnRead
  have taskRaw := callback_load64_raw _ _ _ taskRead
  callback_step
  simp [preemptCountAddress] at preemptRaw ⊢
  rw [preemptRaw]
  simp only [Effects.All]
  callback_step
  dsimp only at returnRaw
  simp [BitVec.signed,returnRaw,Effects.All]
  callback_step
  simp [currentTaskAddress] at taskRaw ⊢
  rw [taskRaw]
  simp only [Effects.All]
  refine eventually_weaken _ _ _ _ ?_ (pc_gate _ ra writes ?_ ?_ ?_ (by rfl))
  · intro t result
    apply stores_post_contract wholePlan
    simpa [StoresPost,Returned] using result
  · simp [pcGatePlan,pcInterruptPlan,pcHardPlan,pcSoftPlan,pcModePlan,pcActivePlan,
      BitVec.extractLsb'_setWidth_of_le,-BitVec.toNat_add]
    by_cases h0 : preempt &&& 0xff0100#32=0#32
    all_goals by_cases h1 : preempt &&& 0x100#32=0#32
    all_goals by_cases h2 : preempt &&& 0xff0000#32=0#32
    all_goals simpa [h0,h1,h2,BitVec.mul_comm,-BitVec.toNat_add] using plan
  · exact frame.2
  · exact ready

theorem pc_image_contract : TracePcContract ServiceImage.fetch := by
  apply leaf_contract
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  exact pc_run s ra ready frame

#print axioms pc_image_contract
end Binary.Callback
