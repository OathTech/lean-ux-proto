import AllowedipsEntryPaths
import CanonicalLoads

namespace Binary.AllowedipsEntry
open TrustBase CommonBitsCoverage CommonBits
local instance : Labels := Image.linkedLabels

/-- The entry's complete physical write frame, widened for either callback
phase so the next anchored fragment uses the same frame. -/
def TotalWrites (initial : MachineState) (coverage : KcovLayout) (old : BitVec 32)
    (a : BitVec 64) : Prop :=
  AllowedipsStackWrites initial a ∨ AllowedipsCoverageWrites coverage old a ∨ InRange preemptCountAddress 4 a

theorem writes_total {initial coverage old a} (written : Writes initial coverage old a) :
    TotalWrites initial coverage old a := by
  rcases written with stack | buffer
  · exact .inl stack
  · exact .inr (.inl ⟨.inl buffer.1,buffer.2⟩)

theorem query_live (initial : MachineState) (bits : Nat) (family : bits=32 ∨ bits=128)
    (a : BitVec 64) (inside : InRange (slot initial 8) (bits/8) a) : AllowedipsLiveStack initial a := by
  obtain ⟨i,hi,eq⟩ := inside
  rw [slot_window initial 8 (by decide)] at eq
  refine ⟨80+i,?_,?_⟩
  · rcases family with rfl | rfl <;> omega
  · simpa only [BitVec.ofNat_add,BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using eq

theorem query_call_apart (initial : MachineState) (bits : Nat) (family : bits=32 ∨ bits=128)
    (a : BitVec 64) (inside : InRange (slot initial 8) (bits/8) a) :
    ¬InRange (slot initial 11) 8 a := by
  rw [slot_window initial 8 (by decide)] at inside
  rw [slot_window initial 11 (by decide)]
  exact InRange.offset_disjoint _ _ _ _ _ (by rcases family with rfl | rfl <;> decide)
    (by decide) (by rcases family with rfl | rfl <;> decide) a inside

structure Post (c : AllowedipsRelation.Config) (initial : MachineState)
    (coverage : KcovLayout) (old : BitVec 32) (ra : UInt64) (s : MachineState) : Prop where
  pc : s.pc=AllowedipsImage.Lookup.entry+0x74
  stack : s.data.regs.rsp=initial.data.regs.rsp-80
  bx : s.data.regs.rbx=.ofBitVec ((initial.data.regs.get (.low .rsi .W32)).setWidth 64)
  bp : s.data.regs.rbp=initial.data.regs.rdx
  r12 : s.data.regs.r12=.ofBitVec ((initial.data.regs.get (.low .rsi .W32)).setWidth 64)
  r13 : s.data.regs.r13=UInt64.ofNat c.bits
  query : AllowedipsChild.QueryWords s.data.dmem (slot initial 8) c.bits c.key
  saved : ∀ i<7, s.data.dmem.loadInt (Allowedips.entrySlot initial.data i) 8 =
    some (((Allowedips.entryWords initial.data)[i]?.getD 0).toNat : Int)
  returnWord : s.data.dmem.loadInt initial.data.regs.rsp.toBitVec 8=some ra.toNat
  mapped : ∀ i<18, (s.data.dmem.loadInt (slot initial (i+1)) 8).isSome=true
  before : AllowedipsCoverageAt coverage old s.data.dmem
  during : AllowedipsCoverageAt coverage (old+512) s.data.dmem
  preempt : load32 s.data.dmem preemptCountAddress=some (old+512)
  ready : CallsReady ⟨coverage,old+512⟩ s.data
  frame : EqualOutside (TotalWrites initial coverage old) initial.data.dmem s.data.dmem

/-- BH-disable writes its real preempt field only after both network reads
have completed. Every saved word, query word and callback field is framed. -/
theorem after_disable {c coverage old ra initial world v s t}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (state : At initial coverage old ra s)
    (query : AllowedipsChild.QueryWords s.dmem (slot initial 8) c.bits c.key)
    (regs : t.data.regs={s.regs with r13 := .ofBitVec ((s.regs.get (.low .r12 .W8)).setWidth 64)})
    (memory : t.data.dmem=s.dmem.storeInt preemptCountAddress 4 (old+512).toInt)
    (pc : t.pc=AllowedipsImage.Lookup.entry+0x74) : Post c initial coverage old ra t := by
  obtain ⟨_,_,physical⟩ := pre.related.2.1
  have family := physical.1.1
  have frame : EqualOutside (InRange preemptCountAddress 4) s.dmem t.data.dmem := by
    rw [memory]; exact storeInt_frame _ _ _ _
  have retained (base : BitVec 64) (width : Nat)
      (inside : ∀ a, InRange base width a → AllowedipsLiveStack initial a) :
      s.dmem.loadInt base width=t.data.dmem.loadInt base width :=
    frame.loadInt base width (fun i hi => pre.preemptStack _ (inside _ ⟨i,hi,rfl⟩))
  have before : AllowedipsCoverageAt coverage old t.data.dmem := by
    apply coverage_metadata_frame ⟨coverage,old⟩ _ _ state.memory.before _ frame
    · intro a member
      exact pre.preemptServices a (.inl (AllowedipsCoverage.metadata_before coverage old a member))
    · intro needed
      exact Kcov.buffer_frame coverage _ _ (state.memory.before.2.2.2 needed).2.2 _ frame
        (fun a stored => pre.preemptServices a (.inr ⟨.inl needed,stored⟩))
  have during : AllowedipsCoverageAt coverage (old+512) t.data.dmem := by
    apply coverage_metadata_frame ⟨coverage,old+512⟩ _ _ state.memory.during _ frame
    · intro a member
      exact pre.preemptServices a (.inl (AllowedipsCoverage.metadata_during coverage old a member))
    · intro needed
      exact Kcov.buffer_frame coverage _ _ (state.memory.during.2.2.2 needed).2.2 _ frame
        (fun a stored => pre.preemptServices a (.inr ⟨.inr needed,stored⟩))
  have preempt : load32 t.data.dmem preemptCountAddress=some (old+512) := by
    rw [memory,load32,load32_store]
    simp only [Option.map_some,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have stack : t.data.regs.rsp=initial.data.regs.rsp-80 := by simp only [regs,state.stack]
  have push : t.data.regs.rsp.toBitVec-8=slot initial 11 := by
    simp only [regs]; exact call_slot state
  have mapped : ∀ i<18, (t.data.dmem.loadInt (slot initial (i+1)) 8).isSome=true := by
    intro i hi
    rw [memory]
    exact storeInt_defined _ _ _ _ _ _ (state.memory.mapped i hi)
  have ready : CallsReady ⟨coverage,old+512⟩ t.data := by
    refine ⟨⟨during,preempt⟩,?_,?_,?_,?_,?_,?_⟩
    · simpa only [regs] using (state.ready pre).aligned
    · rw [push]; exact mapped 10 (by decide)
    · intro a member written
      rw [push] at written
      exact pre.stackServices a (AllowedipsCoverage.bytes_during coverage old a member)
        (slot_writes initial 11 (by decide) (by decide) a written)
    · intro a written inside
      rw [push] at inside
      exact pre.bufferStack a ⟨.inr written.1,written.2⟩ (slot_live initial 11 (by decide) a inside)
    · intro a written metadata
      exact pre.bufferMetadata a ⟨.inr written.1,written.2⟩ (AllowedipsCoverage.metadata_during coverage old a metadata)
    · intro a written inside
      exact pre.bufferPreempt a ⟨.inr written.1,written.2⟩ inside
  refine ⟨pc,stack,by simp only [regs,state.bx],by simp only [regs,state.bp],by simp only [regs,state.r12],
    ?_,?_,?_,?_,mapped,before,during,preempt,ready,?_⟩
  · simp only [regs,(state.family pre).2]
    rcases family with family | family <;> rw [family] <;> rfl
  · exact AllowedipsLoop.query_frame family query frame (fun a read => pre.preemptStack a (query_live initial c.bits family a read))
  · intro i hi
    exact (retained _ 8 (saved_live initial i hi)).symm.trans (state.memory.saved i hi)
  · have inside (a : BitVec 64) (h : InRange initial.data.regs.rsp.toBitVec 8 a) : AllowedipsLiveStack initial a := by
      apply slot_live initial 0 (by decide) a
      simpa only [slot,Nat.zero_mul,BitVec.ofNat_eq_ofNat,BitVec.sub_zero] using h
    exact (retained _ 8 inside).symm.trans state.memory.returnWord
  · intro a outside
    exact (state.frame a (fun h => outside (writes_total h))).trans
      (frame a (fun h => outside (.inr (.inr h))))

#print axioms after_disable
end Binary.AllowedipsEntry
