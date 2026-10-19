import PairRemoveFirstFinish

namespace Binary.Pair.Remove.First
open TrustBase CommonBitsCoverage Index Callback
local instance : Labels := Image.linkedLabels

theorem predecessor (fetch : Int64 → Option Decoded) (agree : IndexRemoveDecoderAgreement fetch)
    {n o c initial ra shadow s} (facts : CallFacts n o c initial ra 4)
    (core : Core c initial ra true shadow s) (layout : Layout o) (f : UnlinkFocus n o shadow)
    (cursor : s.regs.rbx.toBitVec+8=BitVec.ofNat 64 f.removed)
    (previous : s.regs.rbp.toBitVec=BitVec.ofNat 64 f.previous) :
    Eventually (guardedStep fetch (StackGuard initial.data.regs.rsp)) (fun t =>
      t.pc=(if f.next=0 then codeEntry+0x3b else codeEntry+0x31) ∧
      Core c initial ra true (write64 shadow f.previous f.next) t.data ∧
      t.data.regs.rbp=s.regs.rbp ∧ t.data.regs.r12=UInt64.ofNat f.next)
      ⟨s,codeEntry+0x24⟩ := by
  have nextRead := word_loadInt _ _ _ _ _ f.fields.forward
  have nextBound := word_bound f.fields.forward
  rw [layout.next,Nat.add_zero] at nextRead
  have nextSlot := f.fields.nextSlot layout
  rw [layout.next,Nat.add_zero] at nextSlot
  have same := external_read facts.geometry core.frame (nextSlot.heap layout)
  have read : s.dmem.loadInt (s.regs.rbx.toBitVec+8) 8=some (BitVec.ofNat 64 f.next).toNat := by
    rw [cursor,←same]
    simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt nextBound] using nextRead
  have prevRead := word_loadInt _ _ _ _ _ (f.shape.predecessor_read f.member f.fields f.headRead)
  have prevSame := external_read facts.geometry core.frame ((f.previousSlot layout).heap layout)
  have mapped : s.dmem.loadInt s.regs.rbp.toBitVec 8=some (f.removed : Int) := by
    rw [previous,←prevSame]
    exact prevRead
  have run := region_guarded (outer := initial.data.regs.rsp) (IndexMutatorImage.Remove_r24_layout.agreement agree) s _ (by rw [core.stack]; stack_path)
    (predecessor_guard s (.ofNat 64 f.next) f.removed read mapped)
  apply eventually_weaken (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ _ run
  rintro t ⟨registers,memory,pc⟩
  have stored := core.store facts layout (f.previousSlot layout) f.next
  have mem : t.data.dmem=write64 s.dmem f.previous f.next := by
    simpa only [previous,write64] using memory
  have zero : (BitVec.ofNat 64 f.next=0) ↔ f.next=0 := by
    constructor
    · intro equal
      have natEq := congrArg BitVec.toNat equal
      simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt nextBound] using natEq
    · intro equal
      simp [equal]
  refine ⟨by simpa only [zero] using pc,⟨?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · simpa only [registers] using core.stack
  · simpa only [registers] using core.owner
  · simpa only [registers] using core.r13
  · simpa only [registers] using core.r14
  · simpa only [registers] using core.r15
  · simpa only [mem] using stored.memory
  · simpa only [mem] using stored.frame
  · simp only [registers]
  · simp only [registers]
    rfl

theorem successor (fetch : Int64 → Option Decoded) (agree : IndexRemoveDecoderAgreement fetch)
    {n o c initial ra shadow original s} (facts : CallFacts n o c initial ra 4)
    (core : Core c initial ra true shadow s) (layout : Layout o) (f : UnlinkFocus n o original)
    (nonzero : f.next≠0) (next : s.regs.r12.toBitVec=BitVec.ofNat 64 f.next)
    (previous : s.regs.rbp.toBitVec=BitVec.ofNat 64 f.previous)
    (mapped : (shadow.loadInt (.ofNat 64 (f.next+o.pprev)) 8).isSome=true) :
    Eventually (guardedStep fetch (StackGuard initial.data.regs.rsp)) (fun t => t.pc=codeEntry+0x3b ∧
      Core c initial ra true (write64 shadow (f.next+o.pprev) f.previous) t.data ∧
      t.data.regs=s.regs) ⟨s,codeEntry+0x36⟩ := by
  obtain ⟨entry,tail,fields⟩ := f.nextFields nonzero
  have slot := fields.backSlot layout
  have same := external_read facts.geometry core.frame (slot.heap layout)
  have addr : s.regs.r12.toBitVec+8=BitVec.ofNat 64 (f.next+o.pprev) := by
    rw [next,layout.pprev,BitVec.ofNat_add]
    rfl
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp mapped
  have current : s.dmem.loadInt (s.regs.r12.toBitVec+8) 8=some old := by rw [addr,←same,read]
  have run := region_guarded (outer := initial.data.regs.rsp) (IndexMutatorImage.Remove_r36_layout.agreement agree) s _ (by rw [core.stack]; stack_path) (successor_store s old current)
  apply eventually_weaken (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ _ run
  rintro t ⟨registers,memory,pc⟩
  have stored := core.store facts layout slot f.previous
  have mem : t.data.dmem=write64 s.dmem (f.next+o.pprev) f.previous := by
    simpa only [addr,previous,write64] using memory
  exact ⟨pc,⟨by simpa only [registers] using core.stack,by simpa only [registers] using core.owner,
    by simpa only [registers] using core.r13,by simpa only [registers] using core.r14,
    by simpa only [registers] using core.r15,by simpa only [mem] using stored.memory,
    by simpa only [mem] using stored.frame⟩,registers⟩

theorem clear (fetch : Int64 → Option Decoded) (agree : IndexRemoveDecoderAgreement fetch)
    {n o c initial ra shadow original s} (facts : CallFacts n o c initial ra 4)
    (core : Core c initial ra true shadow s) (layout : Layout o) (f : UnlinkFocus n o original)
    (cursor : s.regs.rbx.toBitVec+16=BitVec.ofNat 64 (f.removed+o.pprev))
    (mapped : (shadow.loadInt (.ofNat 64 (f.removed+o.pprev)) 8).isSome=true) :
    Eventually (guardedStep fetch (StackGuard initial.data.regs.rsp)) (fun t => t.pc=codeEntry+0x48 ∧
      Core c initial ra true (write64 shadow (f.removed+o.pprev) 0) t.data)
      ⟨s,codeEntry+0x40⟩ := by
  have slot := f.fields.backSlot layout
  have same := external_read facts.geometry core.frame (slot.heap layout)
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp mapped
  have current : s.dmem.loadInt (s.regs.rbx.toBitVec+16) 8=some old := by rw [cursor,←same,read]
  have run := region_guarded (outer := initial.data.regs.rsp) (IndexMutatorImage.Remove_r40_layout.agreement agree) s _ (by rw [core.stack]; stack_path) (clear_store s old current)
  apply eventually_weaken (guardedStep fetch (StackGuard initial.data.regs.rsp)) _ _ _ _ run
  rintro t ⟨registers,memory,pc⟩
  have stored := core.store facts layout slot 0
  have mem : t.data.dmem=write64 s.dmem (f.removed+o.pprev) 0 := by
    rw [memory,cursor]
    rfl
  exact ⟨pc,⟨by simpa only [registers] using core.stack,by simpa only [registers] using core.owner,
    by simpa only [registers] using core.r13,by simpa only [registers] using core.r14,
    by simpa only [registers] using core.r15,by simpa only [mem] using stored.memory,
    by simpa only [mem] using stored.frame⟩⟩

#print axioms predecessor
#print axioms successor
#print axioms clear
end Binary.Pair.Remove.First
