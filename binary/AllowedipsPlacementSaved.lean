import AllowedipsPlacementFollow

namespace Binary.Pair.Allowedips.Placement
open TrustBase CommonBitsCoverage AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

structure SavedInput (base : MachineData) (c : Context) (bits : BitVec 32) (peer : BitVec 64) : Prop where
  width : base.dmem.loadInt (base.regs.rsp.toBitVec+0x24) 4=some bits.toNat
  owner : base.dmem.loadInt (base.regs.rsp.toBitVec+0x18) 8=some peer.toNat
  separate : ∀ a, InRange (base.regs.rsp.toBitVec+0x24) 4 a ∨
    InRange (base.regs.rsp.toBitVec+0x18) 8 a → ¬Writes base.regs.rsp c a

theorem SavedInput.current {base c bits peer} (input : SavedInput base c bits peer)
    {s} (frame : Frame base c s) :
    s.dmem.loadInt (s.regs.rsp.toBitVec+0x24) 4=some bits.toNat ∧
    s.dmem.loadInt (s.regs.rsp.toBitVec+0x18) 8=some peer.toNat := by
  rw [frame.stack]
  constructor
  · rw [←frame.memory.loadInt _ 4 (fun n bound => input.separate _ (.inl ⟨n,bound,rfl⟩))]
    exact input.width
  · rw [←frame.memory.loadInt _ 8 (fun n bound => input.separate _ (.inr ⟨n,bound,rfl⟩))]
    exact input.owner

theorem SavedInput.restore {base c bits peer} (input : SavedInput base c bits peer)
    (fetch : Int64 → Option Decoded) (mutation : AllowedipsMutationDecoderAgreement fetch)
    {s} (frame : Frame base c s) (parent : BitVec 64)
    (previous : s.dmem.loadInt base.regs.rsp.toBitVec 8=some parent.toNat) :
    Eventually (instructionStep fetch) (fun t => t.pc=Add.entry+0x120 ∧ Frame base c t.data ∧
      t.data.regs.rbp=.ofBitVec (bits.setWidth 64) ∧ t.data.regs.r14=.ofBitVec peer ∧
      t.data.regs.rbx=.ofBitVec parent) ⟨s,Add.entry+0x113⟩ :=
  frame.restore fetch mutation bits peer parent (input.current frame).1 (input.current frame).2
    (by simpa only [frame.stack] using previous)

theorem SavedInput.empty_exit {base c bits peer} (input : SavedInput base c bits peer)
    (fetch : Int64 → Option Decoded) (mutation : AllowedipsMutationDecoderAgreement fetch)
    {s} (frame : Frame base c s) :
    Eventually (instructionStep fetch) (fun t => t.pc=Add.entry+0x120 ∧ Frame base c t.data ∧
      t.data.regs.rbp=.ofBitVec (bits.setWidth 64) ∧ t.data.regs.r14=.ofBitVec peer ∧
      t.data.regs.rbx=s.regs.rbx) ⟨s,Add.entry+0x55f⟩ := by
  have first := region_eventually (Add_r55f_layout.agreement mutation.add) s _
    (empty_restore s bits peer (input.current frame).1 (input.current frame).2)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ first
  rintro t ⟨pc,regs,memory⟩
  exact ⟨pc,frame.congr memory (by simp [regs]) (by simp [regs]) (by simp [regs]) (by simp [regs]),
    by simp [regs],by simp [regs],by simp [regs]⟩

theorem ChildInput.segment {base c address bits query cidr next}
    (input : ChildInput base c address bits query cidr next)
    (fetch : Int64 → Option Decoded) (mutation : AllowedipsMutationDecoderAgreement fetch)
    (pcContract : AllowedipsTracePcContract fetch)
    {s} (frame : Frame base c s) (cursor : s.regs.rbx=address)
    (mapped : (s.dmem.loadInt base.regs.rsp.toBitVec 8).isSome=true) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=(if next=0 then Add.entry+0x55f else Add.entry+0xf7) ∧ Frame base c t.data ∧
      t.data.regs.rbx=(if next=0 then address else .ofBitVec next) ∧
      t.data.dmem.loadInt base.regs.rsp.toBitVec 8=some (address.toNat : Int))
      ⟨s,Add.entry+0xca⟩ := by
  have first := frame.call fetch (Add.entry+0xca) "L_ffffffff810f31f0" .pc pcContract
    (mutation.add _ _ (by rfl))
  apply eventually_trans (instructionStep fetch) _ _ _ first
  rintro t ⟨pc,frame1,bx,_,_,parent⟩
  rw [at_pc t _ pc]
  exact input.follow fetch mutation frame1 (bx.trans cursor) (by rw [frame1.stack,parent]; exact mapped)

#print axioms SavedInput.restore
#print axioms SavedInput.empty_exit
#print axioms ChildInput.segment
end Binary.Pair.Allowedips.Placement
