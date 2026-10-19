import WordAlignment
import CommonBitsEntryHistory

namespace Binary.CommonBits
open TrustBase Instrumentation
local instance : Labels := Image.linkedLabels

def CallerScratch (s : MachineData) : BitVec 64 → Prop := InRange (s.regs.rsp.toBitVec-48) 48

/-- Conditions at lookup's actual common_bits CALL. The conditional data reads
are the helper's reads; stack values are established by the CALL and prologue. -/
structure CallerAt (i : Input) (c : CommonBitsCoverage.Context) (s : MachineData) : Prop where
  node : i.node = s.regs.rdi
  key : i.key = s.regs.rsi
  stack : i.stack = s.regs.rsp-40
  family : i.family = s.regs.get (.low .rdx .W8)
  savedBx : i.savedBx = s.regs.rbx
  savedBp : i.savedBp = s.regs.rbp
  savedR12 : i.savedR12 = s.regs.r12
  savedR13 : i.savedR13 = s.regs.r13
  returnAddress : i.returnAddress = (AllowedipsImage.Lookup.entry+0xea).toUInt64
  keys : ReadsAt i.keyWords s.dmem
  keySeparate : ∀ a, ReadBytes i.keyWords a → ¬(CallerScratch s a ∨ c.writes a)
  coverage : c.At s.dmem
  aligned : s.regs.rsp.toNat % 8 = 0
  mapped : ∀ n < 6, (s.dmem.loadInt (s.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome = true
  coverageSeparate : ∀ a, c.bytes a → ¬CallerScratch s a
  metadataSeparate : ∀ a, c.writes a → ¬c.metadataBytes a
  preemptSeparate : ∀ a, c.writes a → ¬InRange preemptCountAddress 4 a

def helperEntry (s : MachineData) : MachineState :=
  calledState s (AllowedipsImage.Lookup.entry+0xea) AllowedipsImage.CommonBits.entry

private theorem push_inside (s : MachineData) (a : BitVec 64)
    (inside : InRange (s.regs.rsp.toBitVec-8) 8 a) : CallerScratch s a := by
  obtain ⟨n,hn,eq⟩ := inside
  refine ⟨40+n,by omega,?_⟩
  have base : s.regs.rsp.toBitVec-8 = s.regs.rsp.toBitVec-48+40 := by
    change _ = s.regs.rsp.toBitVec-(8+40)+40
    rw [← BitVec.sub_sub,BitVec.sub_add_cancel]
  simpa only [base,BitVec.ofNat_add,BitVec.add_assoc,show (40 : BitVec 64) = 40#64 from rfl] using eq

private theorem helper_scratch (s : MachineData) :
    (helperEntry s).data.regs.rsp.toBitVec-40 = s.regs.rsp.toBitVec-48 := by
  change (s.regs.rsp-8).toBitVec-40 = _
  simp only [UInt64.toBitVec_sub,BitVec.sub_sub]
  rfl

private theorem smaller_inside (base a : BitVec 64) (inside : InRange base 40 a) :
    InRange base 48 a := by
  obtain ⟨n,hn,eq⟩ := inside
  exact ⟨n,by omega,eq⟩

private theorem writes_bytes {c : CommonBitsCoverage.Context} {a : BitVec 64}
    (write : c.writes a) : c.bytes a := .inr (.inr ⟨write.1,.inr write.2⟩)

private theorem stack_base {i c s} (caller : CallerAt i c s) :
    i.stack.toBitVec = s.regs.rsp.toBitVec-48+8 := by
  rw [caller.stack,UInt64.toBitVec_sub]
  change s.regs.rsp.toBitVec-40 = s.regs.rsp.toBitVec-(40+8)+8
  rw [← BitVec.sub_sub,BitVec.sub_add_cancel]

private theorem stack_word {i c s} (caller : CallerAt i c s) (j : Nat) (bound : j < 5)
    (a : BitVec 64) (inside : InRange (i.stack.toBitVec+.ofNat 64 (8*j)) 8 a) :
    ¬i.Writes c a := by
  have base : i.stack.toBitVec+.ofNat 64 (8*j) =
      (s.regs.rsp.toBitVec-48)+.ofNat 64 (8*(j+1)) := by
    rw [stack_base caller]
    have num : 8*(j+1) = 8+8*j := by omega
    rw [num,BitVec.ofNat_add,BitVec.add_assoc]
    rfl
  rw [base] at inside
  intro write
  rcases write with callback | coverage
  · have callbackBase : i.stack.toBitVec-8 = s.regs.rsp.toBitVec-48 := by
      rw [stack_base caller,BitVec.add_sub_cancel]
    rw [callbackBase] at callback
    exact stack_slots_disjoint (s.regs.rsp.toBitVec-48) (j+1) 0 (by omega) (by omega)
      (by omega) a inside (by simpa using callback)
  · apply caller.coverageSeparate a (writes_bytes coverage)
    obtain ⟨n,hn,eq⟩ := inside
    refine ⟨8*(j+1)+n,by omega,?_⟩
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using eq

theorem CallerAt.bodySeparate {i c s} (caller : CallerAt i c s) : i.Separated c := by
  intro a read
  obtain ⟨word,member,inside⟩ := read
  have words : i.words = [⟨i.stack.toBitVec,8,i.savedBx.toNat⟩,
      ⟨i.stack.toBitVec+8,8,i.savedBp.toNat⟩,⟨i.stack.toBitVec+16,8,i.savedR12.toNat⟩,
      ⟨i.stack.toBitVec+24,8,i.savedR13.toNat⟩,⟨i.stack.toBitVec+32,8,i.returnAddress.toNat⟩] ++ i.keyWords := by
    simp [Input.keyWords,Input.words]
  rw [words] at member
  rcases List.mem_append.mp member with saved | key
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at saved
    rcases saved with h | h | h | h | h
    · subst word; exact stack_word caller 0 (by decide) a (by simpa using inside)
    · subst word; exact stack_word caller 1 (by decide) a (by simpa using inside)
    · subst word; exact stack_word caller 2 (by decide) a (by simpa using inside)
    · subst word; exact stack_word caller 3 (by decide) a (by simpa using inside)
    · subst word; exact stack_word caller 4 (by decide) a (by simpa using inside)
  · intro write
    apply caller.keySeparate a ⟨word,key,inside⟩
    rcases write with callback | coverage
    · left
      rw [stack_base caller,BitVec.add_sub_cancel] at callback
      obtain ⟨n,hn,eq⟩ := callback
      exact ⟨n,by omega,eq⟩
    · exact .inr coverage

/-- The CALL's concrete memory store establishes the helper return word. -/
theorem CallerAt.entry {i c s} (caller : CallerAt i c s) : EntryAt i c (helperEntry s).data := by
  have frame : EqualOutside (InRange (s.regs.rsp.toBitVec-8) 8) s.dmem (helperEntry s).data.dmem :=
    storeInt_frame _ _ _ _
  have helperSubset : ∀ a, InRange ((helperEntry s).data.regs.rsp.toBitVec-40) 40 a → CallerScratch s a := by
    intro a inside
    rw [helper_scratch] at inside
    exact smaller_inside _ _ inside
  refine ⟨caller.node,caller.key,?_,caller.family,caller.savedBx,caller.savedBp,
    caller.savedR12,caller.savedR13,?_,?_,?_,?_,?_,?_,?_,caller.metadataSeparate,
    caller.preemptSeparate,caller.bodySeparate⟩
  · rw [caller.stack]
    apply UInt64.toBitVec_inj.mp
    change s.regs.rsp.toBitVec-40 = (s.regs.rsp.toBitVec-8)-32
    rw [BitVec.sub_sub]; rfl
  · rw [caller.returnAddress]
    change (s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 _).loadInt (s.regs.rsp-8).toBitVec 8 = _
    simp only [UInt64.toBitVec_sub,show (8 : UInt64).toBitVec = 8#64 from rfl]
    exact load64_store _ _ _
  · exact caller.keys.frame frame (fun a byte inside => caller.keySeparate a byte (.inl (push_inside s a inside)))
  · intro a byte inside
    exact caller.keySeparate a byte (.inl (helperSubset a inside))
  · exact CommonBitsCoverage.state_frame c _ _ caller.coverage _ frame
      (fun a byte inside => caller.coverageSeparate a byte (push_inside s a inside))
  · change (s.regs.rsp-8).toNat % 8 = 0
    exact aligned_sub _ 8 caller.aligned (by decide)
  · intro n hn
    have mapped := storeInt_defined s.dmem (s.regs.rsp.toBitVec-.ofNat 64 ((n+2)*8))
      (s.regs.rsp.toBitVec-8) 8 8 (AllowedipsImage.Lookup.entry+0xea).toBitVec.toInt
      (caller.mapped (n+1) (by omega))
    change ((helperEntry s).data.dmem.loadInt ((s.regs.rsp-8).toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome = true
    have address : (s.regs.rsp-8).toBitVec-.ofNat 64 ((n+1)*8) =
        s.regs.rsp.toBitVec-.ofNat 64 ((n+2)*8) := by
      rw [UInt64.toBitVec_sub,BitVec.sub_sub]
      have num : (n+2)*8 = 8+(n+1)*8 := by omega
      rw [num,BitVec.ofNat_add]; rfl
    rw [address]
    exact mapped
  · intro a byte inside
    exact caller.coverageSeparate a byte (helperSubset a inside)

theorem CallerAt.callMapped {i c s} (caller : CallerAt i c s) :
    (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true := by
  simpa using caller.mapped 0 (by decide)

theorem CallerAt.returnTarget {i c s} (caller : CallerAt i c s) :
    Int64.ofBitVec i.returnAddress.toBitVec = AllowedipsImage.Lookup.entry+0xea := by
  rw [caller.returnAddress]
  rfl

theorem CallerAt.entryWrites_subset {i c s} (_caller : CallerAt i c s) :
    ∀ a, EntryWrites c (helperEntry s).data a → CallerScratch s a ∨ c.writes a := by
  intro a written
  rcases written with scratch | coverage
  · left
    rw [helper_scratch] at scratch
    exact smaller_inside _ _ scratch
  · exact .inr coverage

/-- Readability of every scratch word survives the helper. The lowest word
comes from the actual callback push; the other five come from saved-word reads. -/
theorem CallerAt.finalMapped {i c s answer final} (caller : CallerAt i c s)
    (post : ReturnPost i c (prologueData (helperEntry s).data 8) answer final) :
    ∀ n < 6, (final.data.dmem.loadInt (s.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome = true := by
  have reads := caller.entry.body.reads.frame post.frame caller.bodySeparate
  have word (j : Nat) (bound : j < 5) :
      (final.data.dmem.loadInt (i.stack.toBitVec+.ofNat 64 (8*j)) 8).isSome = true := by
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
    rcases cases with h | h | h | h | h
    · subst j
      have loaded := reads ⟨i.stack.toBitVec,8,i.savedBx.toNat⟩ (by simp [Input.words])
      simpa using congrArg Option.isSome loaded
    · subst j
      have loaded := reads ⟨i.stack.toBitVec+8,8,i.savedBp.toNat⟩ (by simp [Input.words])
      simpa using congrArg Option.isSome loaded
    · subst j
      have loaded := reads ⟨i.stack.toBitVec+16,8,i.savedR12.toNat⟩ (by simp [Input.words])
      simpa using congrArg Option.isSome loaded
    · subst j
      have loaded := reads ⟨i.stack.toBitVec+24,8,i.savedR13.toNat⟩ (by simp [Input.words])
      simpa using congrArg Option.isSome loaded
    · subst j
      have loaded := reads ⟨i.stack.toBitVec+32,8,i.returnAddress.toNat⟩ (by simp [Input.words])
      simpa using congrArg Option.isSome loaded
  intro n bound
  by_cases last : n=5
  · subst n
    have address : i.stack.toBitVec-8 = s.regs.rsp.toBitVec-.ofNat 64 ((5+1)*8) := by
      rw [caller.stack,UInt64.toBitVec_sub,BitVec.sub_sub]
      rfl
    simpa only [address] using post.callbackMapped
  · have hn : n < 5 := by omega
    have address : i.stack.toBitVec+.ofNat 64 (8*(4-n)) =
        s.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8) := by
      rw [caller.stack,UInt64.toBitVec_sub]
      have num : 40 = (n+1)*8+8*(4-n) := by omega
      change s.regs.rsp.toBitVec-.ofNat 64 40+.ofNat 64 (8*(4-n)) = _
      rw [num,BitVec.ofNat_add,← BitVec.sub_sub,BitVec.sub_add_cancel]
    simpa only [address] using word (4-n) (by omega)

#print axioms CallerAt.finalMapped
#print axioms CallerAt.entry
end Binary.CommonBits
