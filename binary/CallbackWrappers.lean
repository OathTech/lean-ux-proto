import CallbackCmp

namespace Binary.Callback
open TrustBase
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def wrapperState (kind : KcovKind) (s : MachineData) (returnPC : BitVec 64) : MachineData :=
  {s with regs := {s.regs with
    rcx := .ofBitVec returnPC
    rdi := .ofBitVec (KcovRecordTag kind)
    rsi := .ofBitVec (KcovArgument kind ⟨s,0⟩ .rdi)
    rdx := .ofBitVec (KcovArgument kind ⟨s,0⟩ .rsi)}}

theorem wrapper_plan (kind : KcovKind) (notPc : kind≠.pc) (s : MachineData) (pc : Int64)
    (returnPC : BitVec 64) (read : load64 s.dmem s.regs.rsp.toBitVec=some returnPC) :
    cmpPlan (wrapperState kind s returnPC)=KcovPlan kind ⟨s,pc⟩ := by
  simp [cmpPlan,wrapperState,cmpModePlan,cmpActivePlan,KcovPlan,notPc,read,
    BitVec.lt_def,-BitVec.toNat_add,-BitVec.toNat_mul]
  rfl

theorem wrapper_body {rsp : UInt64} (kind : KcovKind) (notPc : kind≠.pc)
    (s : MachineData) (pc : Int64) (ra : UInt64) (returnPC : BitVec 64)
    (read : load64 s.dmem s.regs.rsp.toBitVec=some returnPC)
    (ready : KcovReady kind ⟨s,pc⟩) (frame : EntryFrame ⟨s,pc⟩ ra)
    (stack : s.regs.rsp=rsp) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard rsp))
      (fun t => Returned ⟨s,pc⟩ t ra ∧ EqualOutside (KcovWrites kind ⟨s,pc⟩) s.dmem t.data.dmem ∧
        KcovEffect kind ⟨s,pc⟩ t)
      ⟨wrapperState kind s returnPC,.ofNat 0xffffffff810f3db0⟩ := by
  obtain ⟨writes,plan,ready⟩ := ready
  refine eventually_weaken _ _ _ _ ?_ (cmp_run _ ra writes ?_ ?_ ?_ (by exact stack))
  · intro t result
    apply stores_post_contract plan
    simpa [StoresPost,Returned,wrapperState] using result
  · rw [wrapper_plan kind notPc s pc returnPC read]
    exact plan
  · exact frame.2
  · exact ready


theorem cmp4_run (s : MachineData) (ra : UInt64)
    (ready : KcovReady .cmp4 ⟨s,.ofNat 0xffffffff810f3e80⟩)
    (frame : EntryFrame ⟨s,.ofNat 0xffffffff810f3e80⟩ ra) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard s.regs.rsp))
      (fun t => Returned ⟨s,.ofNat 0xffffffff810f3e80⟩ t ra ∧
        EqualOutside (KcovWrites .cmp4 ⟨s,.ofNat 0xffffffff810f3e80⟩) s.dmem t.data.dmem ∧
        KcovEffect .cmp4 ⟨s,.ofNat 0xffffffff810f3e80⟩ t)
      ⟨s,.ofNat 0xffffffff810f3e80⟩ := by
  have returnRead : load64 s.dmem s.regs.rsp.toBitVec=some ra.toBitVec := by
    simp [load64,frame.2]
  callback_step
  simp [BitVec.signed,frame.2,Effects.All]
  callback_step
  callback_step
  callback_step
  callback_step
  simp [RelRegOrMem.interp,ConstExpr.interp,Effects.All]
  have destination : label "L_ffffffff810f3db0"=.ofNat 0xffffffff810f3db0 := by decide +kernel
  rw [destination]
  simpa [wrapperState,KcovArgument,KcovRecordTag,Reg64s.get,Reg64s.get64,
    Reg.base,Reg.offset,BitVec.drop,BitVec.take] using
    wrapper_body .cmp4 (by decide) s (.ofNat 0xffffffff810f3e80) ra ra.toBitVec
      returnRead ready frame rfl

theorem const_cmp4_run (s : MachineData) (ra : UInt64)
    (ready : KcovReady .constCmp4 ⟨s,.ofNat 0xffffffff810f3f00⟩)
    (frame : EntryFrame ⟨s,.ofNat 0xffffffff810f3f00⟩ ra) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard s.regs.rsp))
      (fun t => Returned ⟨s,.ofNat 0xffffffff810f3f00⟩ t ra ∧
        EqualOutside (KcovWrites .constCmp4 ⟨s,.ofNat 0xffffffff810f3f00⟩) s.dmem t.data.dmem ∧
        KcovEffect .constCmp4 ⟨s,.ofNat 0xffffffff810f3f00⟩ t)
      ⟨s,.ofNat 0xffffffff810f3f00⟩ := by
  have returnRead : load64 s.dmem s.regs.rsp.toBitVec=some ra.toBitVec := by
    simp [load64,frame.2]
  callback_step
  simp [BitVec.signed,frame.2,Effects.All]
  callback_step
  callback_step
  callback_step
  callback_step
  simp [RelRegOrMem.interp,ConstExpr.interp,Effects.All]
  have destination : label "L_ffffffff810f3db0"=.ofNat 0xffffffff810f3db0 := by decide +kernel
  rw [destination]
  simpa [wrapperState,KcovArgument,KcovRecordTag,Reg64s.get,Reg64s.get64,
    Reg.base,Reg.offset,BitVec.drop,BitVec.take] using
    wrapper_body .constCmp4 (by decide) s (.ofNat 0xffffffff810f3f00) ra ra.toBitVec
      returnRead ready frame rfl

theorem const_cmp1_run (s : MachineData) (ra : UInt64)
    (ready : KcovReady .constCmp1 ⟨s,.ofNat 0xffffffff810f3ec0⟩)
    (frame : EntryFrame ⟨s,.ofNat 0xffffffff810f3ec0⟩ ra) :
    Eventually (guardedStep ServiceImage.fetch (leafGuard s.regs.rsp))
      (fun t => Returned ⟨s,.ofNat 0xffffffff810f3ec0⟩ t ra ∧
        EqualOutside (KcovWrites .constCmp1 ⟨s,.ofNat 0xffffffff810f3ec0⟩) s.dmem t.data.dmem ∧
        KcovEffect .constCmp1 ⟨s,.ofNat 0xffffffff810f3ec0⟩ t)
      ⟨s,.ofNat 0xffffffff810f3ec0⟩ := by
  have returnRead : load64 s.dmem s.regs.rsp.toBitVec=some ra.toBitVec := by
    simp [load64,frame.2]
  callback_step
  simp [BitVec.signed,frame.2,Effects.All]
  callback_step
  callback_step
  callback_step
  callback_step
  simp [RelRegOrMem.interp,ConstExpr.interp,Effects.All]
  have destination : label "L_ffffffff810f3db0"=.ofNat 0xffffffff810f3db0 := by decide +kernel
  rw [destination]
  simpa [wrapperState,KcovArgument,KcovRecordTag,Reg64s.get,Reg64s.get64,
    Reg.base,Reg.offset,BitVec.drop,BitVec.take] using
    wrapper_body .constCmp1 (by decide) s (.ofNat 0xffffffff810f3ec0) ra ra.toBitVec
      returnRead ready frame rfl

theorem cmp4_image_contract : TraceCmp4Contract ServiceImage.fetch := by
  apply leaf_contract
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  exact cmp4_run s ra ready frame

#print axioms cmp4_image_contract
theorem const_cmp4_image_contract : TraceConstCmp4Contract ServiceImage.fetch := by
  apply leaf_contract
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  exact const_cmp4_run s ra ready frame

#print axioms const_cmp4_image_contract
theorem const_cmp1_image_contract : TraceConstCmp1Contract ServiceImage.fetch := by
  apply leaf_contract
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  exact const_cmp1_run s ra ready frame

#print axioms const_cmp1_image_contract
end Binary.Callback
