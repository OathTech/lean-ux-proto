import AllowedipsTailPrefix

namespace Binary.AllowedipsTail
open TrustBase CommonBitsCoverage CommonBits AllowedipsEntry Instrumentation
local instance : Labels := Image.linkedLabels

/-- The BH service's actual history includes argument instructions and CALL;
its interiors exclude both sets of anchored correspondence cuts. -/
theorem bh_trace (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (contract : AllowedipsBhEnableContract fetch)
    {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (s : MachineData) (ready : Ready initial coverage old ra s) (rx : Nat) :
    Eventually (historyStep fetch) (fun t =>
      (t.machine.pc=AllowedipsImage.Lookup.entry+0x13c ∧ t.machine.data.regs.rsp=s.regs.rsp ∧
       t.machine.data.dmem.loadInt preemptCountAddress 4=some old.toNat) ∧
      Local (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨ InRange preemptCountAddress 4 a)
        ⟨s,AllowedipsImage.Lookup.entry+0x12b⟩ rx [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x12b⟩,[⟨s,AllowedipsImage.Lookup.entry+0x12b⟩]⟩ := by
  have pending : (old+512+1-512) &&& 0x00ffff00=0 → s.dmem.loadInt softirqPendingAddress 2=some 0 := by
    intro needed
    apply ready.pending
    change (old+1) &&& 0x00ffff00=0
    have arithmetic : old+512+1-512=old+1 := by
      rw [BitVec.add_assoc,BitVec.add_comm (512 : BitVec 32) 1,←BitVec.add_assoc,BitVec.add_sub_cancel]
    simpa only [arithmetic] using needed
  have preemptApart (a : BitVec 64) (read : InRange preemptCountAddress 4 a) :
      ¬InRange (s.regs.rsp.toBitVec-8) 8 a := by
    rw [ready.call_slot]
    intro written
    exact pre.stackServices a (.inr read) (slot_writes initial 11 (by decide) (by decide) a written)
  have pendingApart (needed : (old+512+1-512) &&& 0x00ffff00=0)
      (a : BitVec 64) (read : InRange softirqPendingAddress 2 a) :
      ¬InRange (s.regs.rsp.toBitVec-8) 8 a := by
    rw [ready.call_slot]
    intro written
    have gate : LookupPendingRead old := by
      change (old+1) &&& 0x00ffff00=0
      have arithmetic : old+512+1-512=old+1 := by
        rw [BitVec.add_assoc,BitVec.add_comm (512 : BitVec 32) 1,←BitVec.add_assoc,BitVec.add_sub_cancel]
      simpa only [arithmetic] using needed
    exact pending_separate pre gate a read (.inr (.inl written))
  have run := AllowedipsBh.enable_history fetch agree contract s (old+512)
    ready.calls.aligned ready.calls.mapped (load32_raw _ _ _ ready.calls.state.2) pre.hardirq
    pending preemptApart pendingApart rx [⟨s,AllowedipsImage.Lookup.entry+0x12b⟩] [] rfl rfl
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨returned,count,frame,observed,last,tail,recorded,localLast,noOld,noNew⟩
  have returned' := returned_caller (AllowedipsBh.returnArgument s) (AllowedipsImage.Lookup.entry+0x13c)
    (.ofNat 0xffffffff810732c0) t.machine returned
  have sp : t.machine.data.regs.rsp=s.regs.rsp := by
    simpa only [AllowedipsBh.returnArgument,AllowedipsBh.countArgument,MachineData.setReg,
      Reg64s.set,Reg64s.set64] using returned'.2.1
  refine ⟨⟨returned'.1,sp,by change t.machine.data.dmem.loadInt preemptCountAddress 4=some (old.toNat : Int); simpa only [BitVec.add_sub_cancel] using count⟩,?_,last,⟨[],observed,rfl⟩,frame,?_,?_⟩
  · rw [recorded]; rfl
  · intro q member cut
    rw [recorded] at member
    change q ∈ [⟨s,AllowedipsImage.Lookup.entry+0x12b⟩,
      ⟨AllowedipsBh.countArgument s,AllowedipsImage.Lookup.entry+0x130⟩,
      ⟨AllowedipsBh.returnArgument s,AllowedipsImage.Lookup.entry+0x137⟩] ++ (AllowedipsBh.called s::tail) at member
    rcases List.mem_append.mp member with args | service
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at args
      rcases args with rfl | rfl | rfl <;> intro _ _ <;> rfl
    · rw [←AllowedipsLoop.history_restore localLast] at service
      rcases List.mem_append.mp service with interior | endpoint
      · rcases cut with newCut | oldCut
        · have unmapped := noNew q interior
          have mapped := CommonBits.cut_decoded q.pc newCut
          rw [unmapped] at mapped; cases mapped
        · exact False.elim (LookupObservation.no_reentry_cuts _ noOld q interior oldCut)
      · have equal := List.mem_singleton.mp endpoint
        simpa only [equal] using frame
  · intro q member
    rw [recorded] at member
    change q ∈ (([⟨s,AllowedipsImage.Lookup.entry+0x12b⟩,
      ⟨AllowedipsBh.countArgument s,AllowedipsImage.Lookup.entry+0x130⟩,
      ⟨AllowedipsBh.returnArgument s,AllowedipsImage.Lookup.entry+0x137⟩] : List MachineState) ++ (AllowedipsBh.called s::tail)).dropLast at member
    rw [List.dropLast_append_of_ne_nil (by simp)] at member
    rcases List.mem_append.mp member with args | service
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at args
      rcases args with rfl | rfl | rfl <;>
        change (AllowedipsImage.Lookup.entry+_) ≠ Image.PeerGet.entry+0xaf ∧
          (AllowedipsImage.Lookup.entry+_) ≠ Image.PeerGet.entry+0x4a <;> decide
    · have unmapped := noOld q service
      constructor <;> intro equal <;> rw [equal] at unmapped <;> cases unmapped

#print axioms bh_trace
end Binary.AllowedipsTail
