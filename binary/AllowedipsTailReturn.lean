import AllowedipsTailEnabled

namespace Binary.AllowedipsTail
open TrustBase CommonBitsCoverage CommonBits AllowedipsEntry
local instance : Labels := Image.linkedLabels

structure Post (initial : MachineState) (coverage : KcovLayout) (old : BitVec 32)
    (ra result : UInt64) (s : MachineState) : Prop where
  returned : Returned initial s ra
  result : s.data.regs.rax=result
  before : AllowedipsCoverageAt coverage old s.data.dmem
  during : AllowedipsCoverageAt coverage (old+512) s.data.dmem
  preempt : load32 s.data.dmem preemptCountAddress=some old
  pending : LookupPendingRead old → s.data.dmem.loadInt softirqPendingAddress 2=some 0

theorem restore_address {initial coverage old ra result s}
    (enabled : Enabled initial coverage old ra result s) (i : Nat) (hi : i<6) :
    s.regs.rsp.toBitVec+.ofNat 64 (32+i*8)=Allowedips.entrySlot initial.data (5-i) := by
  rw [enabled.stack,UInt64.toBitVec_sub]
  unfold Allowedips.entrySlot
  rw [if_pos (show 5-i<6 by omega)]
  have number : 80=(5-i+1)*8+(32+i*8) := by omega
  have word : (80 : BitVec 64)=.ofNat 64 ((5-i+1)*8)+.ofNat 64 (32+i*8) := by
    rw [←BitVec.ofNat_add,←number]; rfl
  change initial.data.regs.rsp.toBitVec-80+.ofNat 64 (32+i*8)=_
  rw [word,←BitVec.sub_sub,BitVec.sub_add_cancel]

theorem restore (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    {coverage old ra initial result}
    (s : MachineData) (enabled : Enabled initial coverage old ra result s) (rx : Nat) :
    Eventually (historyStep fetch) (fun t =>
      Post initial coverage old ra result t.machine ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+0x13c⟩ rx
        [(.returned "lookup",none)] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x13c⟩,[⟨s,AllowedipsImage.Lookup.entry+0x13c⟩]⟩ := by
  have h0 : s.dmem.loadInt (s.regs.rsp.toBitVec+32) 8=some initial.data.regs.rbx.toNat := by
    rw [show s.regs.rsp.toBitVec+32=Allowedips.entrySlot initial.data 5 from restore_address enabled 0 (by decide)]
    exact enabled.saved 5 (by decide)
  have h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+40) 8=some initial.data.regs.rbp.toNat := by
    rw [show s.regs.rsp.toBitVec+40=Allowedips.entrySlot initial.data 4 from restore_address enabled 1 (by decide)]
    exact enabled.saved 4 (by decide)
  have h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+48) 8=some initial.data.regs.r12.toNat := by
    rw [show s.regs.rsp.toBitVec+48=Allowedips.entrySlot initial.data 3 from restore_address enabled 2 (by decide)]
    exact enabled.saved 3 (by decide)
  have h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+56) 8=some initial.data.regs.r13.toNat := by
    rw [show s.regs.rsp.toBitVec+56=Allowedips.entrySlot initial.data 2 from restore_address enabled 3 (by decide)]
    exact enabled.saved 2 (by decide)
  have h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+64) 8=some initial.data.regs.r14.toNat := by
    rw [show s.regs.rsp.toBitVec+64=Allowedips.entrySlot initial.data 1 from restore_address enabled 4 (by decide)]
    exact enabled.saved 1 (by decide)
  have h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+72) 8=some initial.data.regs.r15.toNat := by
    rw [show s.regs.rsp.toBitVec+72=Allowedips.entrySlot initial.data 0 from restore_address enabled 5 (by decide)]
    exact enabled.saved 0 (by decide)
  have h6 : s.dmem.loadInt (s.regs.rsp.toBitVec+80) 8=some ra.toNat := by
    rw [enabled.stack,UInt64.toBitVec_sub]
    change s.dmem.loadInt (initial.data.regs.rsp.toBitVec-80+80) 8=some ra.toNat
    rw [BitVec.sub_add_cancel]; exact enabled.returnWord
  have run := Allowedips.epilogue_trace fetch agree s result initial.data.regs.rbx initial.data.regs.rbp
    initial.data.regs.r12 initial.data.regs.r13 initial.data.regs.r14 initial.data.regs.r15 ra
    enabled.value h0 h1 h2 h3 h4 h5 h6 rx
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨⟨regs,memory,pc⟩,trace⟩
  refine ⟨⟨?_,by simp only [regs],by simpa only [memory] using enabled.before,
    by simpa only [memory] using enabled.during,?_,by simpa only [memory] using enabled.pending⟩,
    trace.mono (fun _ h => h.elim)⟩
  · refine ⟨pc,?_,by simp only [regs],by simp only [regs],by simp only [regs],
      by simp only [regs],by simp only [regs],by simp only [regs]⟩
    simp only [regs,enabled.stack]
    apply UInt64.toBitVec_inj.mp
    change initial.data.regs.rsp.toBitVec-80+88=initial.data.regs.rsp.toBitVec+8
    rw [show (88 : BitVec 64)=80+8 from rfl,←BitVec.add_assoc,BitVec.sub_add_cancel]
  · rw [memory,load32]
    have field : s.dmem.loadInt preemptCountAddress 4=some (old.toNat : Int) := enabled.preempt
    rw [field]
    simp only [Option.map_some,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]

#print axioms restore
end Binary.AllowedipsTail
