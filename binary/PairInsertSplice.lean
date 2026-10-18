import PairInsertHeapFrame
import PairInsertLinkRegions

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

theorem unlink_predecessor (fetch : Int64 → Option Decoded) (agree : IndexInsertDecoderAgreement fetch)
    {n o c initial ra shadow s} (facts : FrameFacts n o c initial ra)
    (core : Core n o c initial ra .outer shadow s) (layout : Layout o) (f : UnlinkFocus n o shadow)
    (cursor : s.regs.rbp.toBitVec+8=BitVec.ofNat 64 f.removed)
    (previous : s.regs.rbx.toBitVec=BitVec.ofNat 64 f.previous) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=(if f.next=0 then codeEntry+0x42 else codeEntry+0x39) ∧
      Core n o c initial ra .outer (write64 shadow f.previous f.next) t.data ∧
      t.data.regs.rbx=s.regs.rbx ∧ t.data.regs.r13=UInt64.ofNat f.next)
      ⟨s,codeEntry+0x2d⟩ := by
  have nextRead := word_loadInt _ _ _ _ _ f.fields.forward
  have nextBound := word_bound f.fields.forward
  rw [layout.next,Nat.add_zero] at nextRead
  have nextSlot := f.fields.nextSlot layout
  rw [layout.next,Nat.add_zero] at nextSlot
  have same := core.frame.loadInt _ _ (nextSlot.heap layout)
  have read : s.dmem.loadInt (s.regs.rbp.toBitVec+8) 8=some (BitVec.ofNat 64 f.next).toNat := by
    rw [cursor,←same]
    simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt nextBound] using nextRead
  have prevRead := word_loadInt _ _ _ _ _ (f.shape.predecessor_read f.member f.fields f.headRead)
  have prevSame := core.frame.loadInt _ _ ((f.previousSlot layout).heap layout)
  have mapped : s.dmem.loadInt s.regs.rbx.toBitVec 8=some (f.removed : Int) := by
    rw [previous,←prevSame]
    exact prevRead
  have run := region_eventually (IndexInsertImage.Insert_r2d_layout.agreement agree) s _
    (predecessor s (.ofNat 64 f.next) f.removed read mapped)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨registers,memory,pc⟩
  have stored := core.store64 facts layout (f.previousSlot layout) f.next
  have mem : t.data.dmem=write64 s.dmem f.previous f.next := by
    simpa only [previous,write64] using memory
  have zero : (BitVec.ofNat 64 f.next=0) ↔ f.next=0 := by
    constructor
    · intro equal
      have natEq := congrArg BitVec.toNat equal
      simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt nextBound] using natEq
    · intro equal
      simp [equal]
  refine ⟨by simpa only [zero] using pc,⟨?_,?_,?_,?_,?_⟩,?_,?_⟩
  · simpa only [registers] using core.stack
  · simpa only [registers] using core.table
  · simpa only [registers] using core.owner
  · simpa only [mem] using stored.memory
  · simpa only [mem] using stored.frame
  · simp only [registers]
  · simp only [registers]
    rfl

theorem unlink_successor_endpoint (fetch : Int64 → Option Decoded) (agree : IndexInsertDecoderAgreement fetch)
    {n o c initial ra shadow original s} (facts : FrameFacts n o c initial ra)
    (core : Core n o c initial ra .outer shadow s) (layout : Layout o) (f : UnlinkFocus n o original)
    (nonzero : f.next≠0) (next : s.regs.r13.toBitVec=BitVec.ofNat 64 f.next)
    (previous : s.regs.rbx.toBitVec=BitVec.ofNat 64 f.previous)
    (mapped : (shadow.loadInt (.ofNat 64 (f.next+o.pprev)) 8).isSome=true) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x42 ∧
      Core n o c initial ra .outer (write64 shadow (f.next+o.pprev) f.previous) t.data ∧
      t.data.regs=s.regs) ⟨s,codeEntry+0x3e⟩ := by
  obtain ⟨entry,tail,fields⟩ := f.nextFields nonzero
  have slot := fields.backSlot layout
  have same := core.frame.loadInt _ _ (slot.heap layout)
  have addr : s.regs.r13.toBitVec+8=BitVec.ofNat 64 (f.next+o.pprev) := by
    rw [next,layout.pprev,BitVec.ofNat_add]
    rfl
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp mapped
  have current : s.dmem.loadInt (s.regs.r13.toBitVec+8) 8=some old := by rw [addr,←same,read]
  have run := region_eventually (IndexInsertImage.Insert_r3e_layout.agreement agree) s _ (unlink_successor s old current)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨registers,memory,pc⟩
  have stored := core.store64 facts layout slot f.previous
  have mem : t.data.dmem=write64 s.dmem (f.next+o.pprev) f.previous := by
    simpa only [addr,previous,write64] using memory
  exact ⟨pc,⟨by simpa only [registers] using core.stack,by simpa only [registers] using core.table,
    by simpa only [registers] using core.owner,by simpa only [mem] using stored.memory,
    by simpa only [mem] using stored.frame⟩,registers⟩

theorem unlink_clear_endpoint (fetch : Int64 → Option Decoded) (agree : IndexInsertDecoderAgreement fetch)
    {n o c initial ra shadow original s} (facts : FrameFacts n o c initial ra)
    (core : Core n o c initial ra .outer shadow s) (layout : Layout o) (f : UnlinkFocus n o original)
    (cursor : s.regs.rbp.toBitVec+16=BitVec.ofNat 64 (f.removed+o.pprev))
    (mapped : (shadow.loadInt (.ofNat 64 (f.removed+o.pprev)) 8).isSome=true) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x4f ∧
      Core n o c initial ra .outer (write64 shadow (f.removed+o.pprev) 0) t.data)
      ⟨s,codeEntry+0x47⟩ := by
  have slot := f.fields.backSlot layout
  have same := core.frame.loadInt _ _ (slot.heap layout)
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp mapped
  have current : s.dmem.loadInt (s.regs.rbp.toBitVec+16) 8=some old := by rw [cursor,←same,read]
  have run := region_eventually (IndexInsertImage.Insert_r47_layout.agreement agree) s _ (clear s old current)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨registers,memory,pc⟩
  have stored := core.store64 facts layout slot 0
  have mem : t.data.dmem=write64 s.dmem (f.removed+o.pprev) 0 := by
    rw [memory,cursor]
    rfl
  exact ⟨pc,⟨by simpa only [registers] using core.stack,by simpa only [registers] using core.table,
    by simpa only [registers] using core.owner,by simpa only [mem] using stored.memory,
    by simpa only [mem] using stored.frame⟩⟩

#print axioms unlink_predecessor
#print axioms unlink_successor_endpoint
#print axioms unlink_clear_endpoint
end Binary.Pair.Insert
