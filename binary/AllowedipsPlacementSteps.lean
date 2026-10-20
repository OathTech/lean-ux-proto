import AllowedipsPlacementFrame
import AllowedipsPlacementCalls
import AllowedipsCommonChecked

namespace Binary.Pair.Allowedips.Placement
open TrustBase CommonBitsCoverage AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

theorem Frame.call (fetch : Int64 → Option Decoded) (pc : Int64) (target : Label)
    (kind : KcovKind)
    (contract : AllowedipsServiceReturns fetch (label target) (KcovReady kind) (KcovWrites kind) (KcovEffect kind))
    (here : fetch pc=some ⟨Instrumentation.callInstruction target,5⟩)
    {base c s} (frame : Frame base c s) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=pc+5 ∧ Frame base c t.data ∧ t.data.regs.rbx=s.regs.rbx ∧
      t.data.regs.rbp=s.regs.rbp ∧ t.data.regs.r14=s.regs.r14 ∧
      t.data.dmem.loadInt base.regs.rsp.toBitVec 8=s.dmem.loadInt base.regs.rsp.toBitVec 8) ⟨s,pc⟩ := by
  apply frame.region_callback fetch (label target) (pc+5) kind contract _ s.regs rfl rfl rfl
  apply Sequential.forget
    (historySteps_eventually fetch 1 _ _
      (Instrumentation.call_instruction fetch pc target here s [] frame.ready.mapped))
  rintro t ⟨machine,_⟩
  simp [machine,Instrumentation.calledState]

theorem Frame.cidr_arguments (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch) (cmp : AllowedipsTraceCmp1Contract fetch)
    {base c s} (frame : Frame base c s) (cidr : BitVec 8)
    (read : s.dmem.loadInt (s.regs.rbx.toBitVec+24) 1=some cidr.toNat) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x10a ∧ Frame base c t.data ∧ t.data.regs.rbx=s.regs.rbx ∧
      t.data.regs.rbp=.ofBitVec (cidr.setWidth 64) ∧ t.data.regs.r14=s.regs.r14 ∧
      t.data.dmem.loadInt base.regs.rsp.toBitVec 8=s.dmem.loadInt base.regs.rsp.toBitVec 8)
      ⟨s,Add.entry+0xfc⟩ := by
  obtain ⟨old,mapped⟩ := Option.isSome_iff_exists.mp frame.ready.mapped
  apply frame.region_callback fetch (.ofNat 0xffffffff810f4040) (Add.entry+0x10a) .cmp1 cmp _
    {s.regs with
      rbp := .ofBitVec (cidr.setWidth 64),
      rdi := .ofBitVec ((s.regs.get (.low .r12 .W32)).setWidth 64),rsi := .ofBitVec (cidr.setWidth 64)}
    rfl rfl rfl
  exact region_eventually (Add_rfc_layout.agreement decoder.add) s _ (Placement.cidr_arguments s cidr old read mapped)

theorem Frame.prefix_arguments (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch) (cmp : AllowedipsTraceCmp1Contract fetch)
    {base c s} (frame : Frame base c s) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0xad ∧ Frame base c t.data ∧ t.data.regs.rbx=s.regs.rbx ∧
      t.data.regs.rbp=s.regs.rbp ∧
      t.data.regs.r14=.ofBitVec ((s.regs.get (.low .rax .W32)).setWidth 64) ∧
      t.data.dmem.loadInt base.regs.rsp.toBitVec 8=s.dmem.loadInt base.regs.rsp.toBitVec 8) ⟨s,Add.entry+0xa1⟩ := by
  obtain ⟨old,mapped⟩ := Option.isSome_iff_exists.mp frame.ready.mapped
  apply frame.region_callback fetch (.ofNat 0xffffffff810f4040) (Add.entry+0xad) .cmp1 cmp _
    {s.regs with
      rdi := .ofBitVec ((s.regs.get (.low .rbp .W32)).setWidth 64),
      r14 := .ofBitVec ((s.regs.get (.low .rax .W32)).setWidth 64),
      rsi := .ofBitVec ((s.regs.get (.low .rax .W32)).setWidth 64)} rfl rfl rfl
  exact region_eventually (Add_ra1_layout.agreement decoder.add) s _ (Placement.prefix_arguments s old mapped)

theorem Frame.exact_arguments (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsMutationDecoderAgreement fetch) (cmp : AllowedipsTraceCmp1Contract fetch)
    {base c s} (frame : Frame base c s) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0xc1 ∧ Frame base c t.data ∧ t.data.regs.rbx=s.regs.rbx ∧
      t.data.regs.rbp=s.regs.rbp ∧ t.data.regs.r14=s.regs.r14 ∧
      t.data.dmem.loadInt base.regs.rsp.toBitVec 8=s.dmem.loadInt base.regs.rsp.toBitVec 8) ⟨s,Add.entry+0xb7⟩ := by
  obtain ⟨old,mapped⟩ := Option.isSome_iff_exists.mp frame.ready.mapped
  apply frame.region_callback fetch (.ofNat 0xffffffff810f4040) (Add.entry+0xc1) .cmp1 cmp _
    {s.regs with
      rdi := .ofBitVec ((s.regs.get (.low .r12 .W32)).setWidth 64),
      rsi := .ofBitVec ((s.regs.get (.low .rbp .W32)).setWidth 64)} rfl rfl rfl
  exact region_eventually (Add_rb7_layout.agreement decoder.add) s _ (Placement.exact_arguments s old mapped)

theorem Frame.common (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsDecoderAgreement fetch) (callbacks : CommonBits.Callbacks fetch)
    (pc : Int64) (here : fetch pc=some ⟨Instrumentation.callInstruction "L_ffffffff813a0950",5⟩)
    (i : CommonBits.Input) {base c s} (frame : Frame base c s)
    (caller : CommonBits.CallerAt i c s (pc+5)) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=pc+5 ∧ Frame base c t.data ∧ t.data.regs.rbx=s.regs.rbx ∧
      t.data.regs.rbp=s.regs.rbp ∧ (t.data.regs.get (.low .rax .W8)).toNat=i.result ∧
      t.data.dmem.loadInt base.regs.rsp.toBitVec 8=s.dmem.loadInt base.regs.rsp.toBitVec 8) ⟨s,pc⟩ := by
  have executed := CommonBits.Sequential.call_run fetch decoder callbacks pc here i c s caller
  apply eventually_weaken (instructionStep fetch) _ _ _ _ executed
  rintro t ⟨pc,sp,bx,bp,r12,r13,_,r15,answer,covered,written,mapped⟩
  refine ⟨pc,?_,bx,bp,answer,frame.parent_preserved written⟩
  apply frame.after sp r13 r12 r15 covered
  · simpa only [frame.stack] using mapped
  · intro a outside
    apply written a
    rintro (scratch | buffer)
    · exact outside (.inl (scratch_subset (by simpa only [CommonBits.CallerScratch,frame.stack] using scratch)))
    · exact outside (.inr buffer)

#print axioms Frame.cidr_arguments
#print axioms Frame.prefix_arguments
#print axioms Frame.exact_arguments
#print axioms Frame.common
end Binary.Pair.Allowedips.Placement
