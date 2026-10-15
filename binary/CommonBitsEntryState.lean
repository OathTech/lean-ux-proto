import CommonBitsPrologue
import CommonBitsBodyState

namespace Binary.CommonBits
open TrustBase

/-- The conditional data reads, without words that the prologue itself saves. -/
def Input.keyWords (i : Input) : List ReadWord := i.words.drop 5

def EntryWrites (c : CommonBitsCoverage.Context) (s : MachineData) (a : BitVec 64) : Prop :=
  InRange (s.regs.rsp.toBitVec-40) 40 a ∨ c.writes a

/-- Physical entry facts only. Saved words are established by execution below. -/
structure EntryAt (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData) : Prop where
  node : i.node = s.regs.rdi
  key : i.key = s.regs.rsi
  stack : i.stack = s.regs.rsp-32
  family : i.family = s.regs.get (.low .rdx .W8)
  savedBx : i.savedBx = s.regs.rbx
  savedBp : i.savedBp = s.regs.rbp
  savedR12 : i.savedR12 = s.regs.r12
  savedR13 : i.savedR13 = s.regs.r13
  returnWord : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (i.returnAddress.toNat : Int)
  keys : ReadsAt i.keyWords s.dmem
  keySeparate : ∀ a, ReadBytes i.keyWords a → ¬InRange (s.regs.rsp.toBitVec-40) 40 a
  coverage : c.At s.dmem
  aligned : s.regs.rsp.toNat % 8 = 0
  mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome = true
  coverageSeparate : ∀ a, c.bytes a → ¬InRange (s.regs.rsp.toBitVec-40) 40 a
  metadataSeparate : ∀ a, c.writes a → ¬c.metadataBytes a
  preemptSeparate : ∀ a, c.writes a → ¬InRange preemptCountAddress 4 a
  bodySeparate : i.Separated c

private theorem stack_offset (s : MachineData) (n : Nat) (bound : n ≤ 4) :
    (s.regs.rsp-32).toBitVec + .ofNat 64 (8*n) =
      s.regs.rsp.toBitVec - .ofNat 64 (32-8*n) := by
  rw [UInt64.toBitVec_sub, show (32 : UInt64).toBitVec = 32#64 from rfl]
  have num : 32 = (32-8*n)+8*n := by omega
  change s.regs.rsp.toBitVec - .ofNat 64 32 + .ofNat 64 (8*n) = _
  rw [num, BitVec.ofNat_add,
    ← BitVec.sub_sub, BitVec.sub_add_cancel]
  simp only [Nat.add_sub_cancel]

private theorem body_word_in_scratch (s : MachineData) (a : BitVec 64)
    (inside : InRange ((s.regs.rsp-32).toBitVec-8) 8 a) :
    InRange (s.regs.rsp.toBitVec-40) 40 a := by
  obtain ⟨n,hn,atByte⟩ := inside
  refine ⟨n,by omega,?_⟩
  simpa only [UInt64.toBitVec_sub, show (32 : UInt64).toBitVec = 32#64 from rfl,
    BitVec.sub_sub, show (32#64+8 : BitVec 64) = 40 from rfl] using atByte

theorem EntryAt.writes_subset {i c s} (entry : EntryAt i c s) :
    ∀ a, i.Writes c a → EntryWrites c s a := by
  intro a write
  rcases write with stack | coverage
  · exact .inl (body_word_in_scratch s a (by simpa only [entry.stack] using stack))
  · exact .inr coverage

theorem EntryAt.body {i c s} (entry : EntryAt i c s) : BodyAt i c (prologueData s 8) := by
  have frame := saveMemory_frame s 4 (by decide)
  have coverage : c.At (saveMemory s 4) :=
    CommonBitsCoverage.state_frame c _ _ entry.coverage _ frame entry.coverageSeparate
  have stack : (prologueData s 8).regs.rsp = i.stack := by
    change s.regs.rsp-32 = i.stack
    exact entry.stack.symm
  have keyReads : ReadsAt i.keyWords (saveMemory s 4) := entry.keys.frame frame entry.keySeparate
  refine ⟨?_,stack,?_,?_,?_⟩
  · refine ⟨coverage,?_,?_,?_,?_,entry.metadataSeparate,entry.preemptSeparate⟩
    · change (s.regs.rsp-32).toNat % 8 = 0
      simp only [UInt64.toNat_sub,show (32 : UInt64).toNat = 32 from rfl]
      have bound := s.regs.rsp.toNat_lt_size
      have aligned := entry.aligned
      omega
    · have mapped := saves_preserve_mapped s 4 _ (entry.mapped 4 (by decide))
      change ((saveMemory s 4).loadInt ((s.regs.rsp-32).toBitVec-8) 8).isSome = true
      simpa [UInt64.toBitVec_sub,BitVec.sub_sub] using mapped
    · intro a byte inside
      exact entry.coverageSeparate a byte (body_word_in_scratch s a inside)
    · intro a write inside
      exact entry.coverageSeparate a (.inr (.inr ⟨write.1,.inr write.2⟩))
        (body_word_in_scratch s a inside)
  · simpa [prologueData] using entry.node.symm
  · simpa [prologueData] using entry.key.symm
  · have h0 := saveMemory_read s 4 3 (by decide) (by decide)
    have h1 := saveMemory_read s 4 2 (by decide) (by decide)
    have h2 := saveMemory_read s 4 1 (by decide) (by decide)
    have h3 := saveMemory_read s 4 0 (by decide) (by decide)
    have h4 := (saveMemory_return s 4 (by decide)).trans entry.returnWord
    have a0 : i.stack.toBitVec = slot s 3 := by
      rw [entry.stack]; rfl
    have a1 : i.stack.toBitVec+8 = slot s 2 := by
      simpa [entry.stack,slot] using stack_offset s 1 (by decide)
    have a2 : i.stack.toBitVec+16 = slot s 1 := by
      simpa [entry.stack,slot] using stack_offset s 2 (by decide)
    have a3 : i.stack.toBitVec+24 = slot s 0 := by
      simpa [entry.stack,slot] using stack_offset s 3 (by decide)
    have a4 : i.stack.toBitVec+32 = s.regs.rsp.toBitVec := by
      simpa [entry.stack] using stack_offset s 4 (by decide)
    have words : i.words = [⟨i.stack.toBitVec,8,i.savedBx.toNat⟩,
        ⟨i.stack.toBitVec+8,8,i.savedBp.toNat⟩,⟨i.stack.toBitVec+16,8,i.savedR12.toNat⟩,
        ⟨i.stack.toBitVec+24,8,i.savedR13.toNat⟩,⟨i.stack.toBitVec+32,8,i.returnAddress.toNat⟩] ++ i.keyWords := by
      simp [Input.keyWords,Input.words]
    intro word member
    rw [words] at member
    rcases List.mem_append.mp member with saved | key
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at saved
      rcases saved with h | h | h | h | h
      · subst word; simpa only [prologueData,savedCount,a0,entry.savedBx,savedWords,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using h0
      · subst word; simpa only [prologueData,savedCount,a1,entry.savedBp,savedWords,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using h1
      · subst word; simpa only [prologueData,savedCount,a2,entry.savedR12,savedWords,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using h2
      · subst word; simpa only [prologueData,savedCount,a3,entry.savedR13,savedWords,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some] using h3
      · subst word; simpa only [prologueData,savedCount,a4] using h4
    · exact keyReads word key

private theorem low_byte (v : BitVec 64) :
    ((v.extractLsb' 0 32).setWidth 64).extractLsb' 0 8 = v.extractLsb' 0 8 := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem EntryAt.family_bytes {i c s} (entry : EntryAt i c s) :
    (prologueData s 8).regs.get (.low .rbx .W8) = i.family ∧
    (prologueData s 8).regs.get (.low .rbp .W8) = i.family := by
  rw [entry.family]
  simp [prologueData,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,
    BitVec.drop,BitVec.take,low_byte]

end Binary.CommonBits
