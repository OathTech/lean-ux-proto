import LookupFromPre
import LookupFirstEntrySimulation
import LookupFirstBucketSimulation
namespace Binary.LookupRelation.First
open Leanux TrustBase LookupHistory Callback
local instance : Labels := Image.linkedLabels

theorem start_from_entry (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : LeafService fetch (.ofNat 0xffffffff810f31f0) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc))
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v) :
    Eventually (guardedHistoryStep fetch (StackGuard s.regs.rsp)) (Started c world s ⟨coverage, preempt, v⟩ preempt)
      ⟨⟨s, Image.Lookup.entry⟩, [⟨s, Image.Lookup.entry⟩]⟩ := by
  let context : LookupCoverage.Context := ⟨coverage, preempt, v⟩
  have words : 6 ≤ LookupStackWords c := by
    unfold LookupStackWords
    split <;> decide
  have stackSubset (a : BitVec 64) (inside : InRange (s.regs.rsp.toBitVec-48) 48 a) :
      LookupStackWrites c ⟨s, Image.Lookup.entry⟩ a :=
    backwards_range s.regs.rsp.toBitVec 48 (8*LookupStackWords c) 0 (by omega) a inside
  have returnSubset (a : BitVec 64) (inside : InRange (s.regs.rsp.toBitVec-48) 8 a) :
      LookupLiveStack c ⟨s, Image.Lookup.entry⟩ a := by
    apply backwards_range s.regs.rsp.toBitVec 48 (8*LookupStackWords c) 8 (by omega) a
    obtain ⟨i, hi, eq⟩ := inside
    exact ⟨i, by omega, eq⟩
  have related := entry_R c world s v entry.projected entry.physical entry.steps entry.rxSection
  apply start_simulation fetch agree tracePc c world s context preempt related
    ⟨entry.coverageAt, entry.preemptAt⟩ (.inl rfl) entry.frame.1
    (fun i hi => entry.stackMapped i (by omega))
    (fun a read written => entry.serviceStack a read (stackSubset a written))
    (fun a written read => entry.coverageStack a written (returnSubset a read))
    entry.coverageMetadata entry.coveragePreempt
  intro other projected a read written
  have eq : other = v := Option.some.inj (projected.symm.trans entry.projected)
  subst other
  rcases written with stack | buffer
  · exact entry.readsScratch a read (.inl (stackSubset a stack))
  · exact entry.readsScratch a read (.inr (.inl buffer))

/-- Non-vacuous entry declaration to actual executed prologue, for its
    projected view. The witness in LookupWitness is one concrete instance. -/private theorem low32_ofNat (v : BitVec 32) :
    (UInt64.ofNat v.toNat).toBitVec.extractLsb' 0 32 = v := by
  apply BitVec.eq_of_toNat_eq
  simp
  exact v.isLt

theorem header_from_started (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v)
    (u : Executed) (started : Started c world s ⟨coverage, preempt, v⟩ preempt u) :
    Eventually (guardedHistoryStep fetch (StackGuard s.regs.rsp)) (BeforeBucket c world s ⟨coverage, preempt, v⟩ preempt) u := by
  obtain ⟨pc, sp, bx, query, out, mask, saved, ready, memory, raw, observed,
    matched, aligned, related, stable, tail⟩ := started
  have table : u.machine.data.regs.rbx.toBitVec = c.table := by rw [bx]; exact entry.table
  have queryReg : (u.machine.data.regs.get (.low .r12 .W32)).toNat = c.query := by
    simp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, Width.bits, Nat.sub_zero, BitVec.extractLsb'_eq_self]
    change (u.machine.data.regs.r12.toBitVec.extractLsb' 0 32).toNat = _
    rw [query, low32_ofNat]
    exact entry.query
  have kindReg : KindMask (u.machine.data.regs.get (.low .r14 .W32)) c.kinds := by
    simp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, Width.bits, Nat.sub_zero, BitVec.extractLsb'_eq_self]
    change KindMask (u.machine.data.regs.r14.toBitVec.extractLsb' 0 32) _
    rw [mask, low32_ofNat]
    exact entry.kinds
  have run := header_simulation (outer := s.regs.rsp) fetch agree c world u.machine.data (by rw [sp]; stack_not_return)
    ⟨coverage, preempt, v⟩ preempt ready rfl table queryReg
    (fun a h => entry.bhMetadata a (.inl h))
    (fun needed a h => entry.bhMetadata a (.inr ⟨needed,h⟩))
    (by
      intro other projected a read written
      have eq : other = v := Option.some.inj (projected.symm.trans entry.projected)
      subst other
      exact entry.readsScratch a read (.inr (.inr written)))
    u.history [entryPoint s] [] [sourceEntry world]
    (by simpa only [← pc] using related) observed raw matched aligned rfl (by rfl) (by rfl)
  have cursor : (⟨⟨u.machine.data, Image.Lookup.entry+0x19⟩, u.history⟩ : Executed) = u := by
    cases u with | mk machine history => cases machine; simp_all
  rw [cursor] at run
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _ _ run
  rintro t ⟨pc', ⟨head, regs⟩, ready', loaded, memory', raw', observed',
    matched', aligned', related', stable', suffix, recorded, frames⟩
  refine ⟨pc', by simpa only [regs] using sp,
    by simpa only [regs, Reg64s.get, Reg64s.get64, Reg.base] using queryReg, by simpa only [regs] using out,
    by simpa only [regs, Reg64s.get, Reg64s.get64, Reg.base] using kindReg, by simpa only [regs] using saved,
    ready', loaded, memory.trans memory', raw', observed', matched', aligned', related', stable.trans stable', ?_⟩
  obtain ⟨prefixTail, prefixEq, prefixFrames⟩ := tail
  have old : CutFrames (fun a => Lookup.entryWrites s ⟨coverage, preempt, v⟩ a ∨ InRange preemptCountAddress 4 a) s.dmem u.history := by
    rw [prefixEq]
    exact (CutFrames.initial _ _).append_after (fun _ _ => rfl) prefixFrames (fun _ => Or.inl)
  have endpoint : EqualOutside (fun a => Lookup.entryWrites s ⟨coverage, preempt, v⟩ a ∨ InRange preemptCountAddress 4 a) s.dmem u.machine.data.dmem := by
    intro a outside
    exact (Lookup.saveMemory_frame s 6 (by decide) a (fun inside => outside (.inl (.inl inside)))).trans
      (memory a (fun inside => outside (.inl (.inr inside))))
  rw [recorded]
  exact old.append_after endpoint frames (fun _ => Or.inr)
theorem bucket_from_head (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : LeafService fetch (.ofNat 0xffffffff810f31f0) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc))
    (traceCmp : LeafService fetch (.ofNat 0xffffffff810f4080) (KcovReady .cmp4) (KcovWrites .cmp4) (KcovEffect .cmp4)) (traceConstCmp : LeafService fetch (.ofNat 0xffffffff810f4100) (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4))
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v)
    (head : Executed) (atHead : BeforeBucket c world s ⟨coverage, preempt, v⟩ preempt head) :
    Eventually (guardedHistoryStep fetch (StackGuard s.regs.rsp)) (AfterBucket c world s coverage preempt v) head := by
  have apart : ∀ a, Reads c v a → ¬scanWrites head.machine.data ⟨coverage, preempt, v⟩ a := by
    intro a read written
    apply entry.readsScratch a read
    rcases written with stack | buffer
    · apply Or.inl
      have loc : head.machine.data.regs.rsp.toBitVec-8 = s.regs.rsp.toBitVec-48 := by
        rw [atHead.stack, UInt64.toBitVec_sub, BitVec.sub_sub]
        rfl
      rw [loc] at stack
      have words : 6 ≤ LookupStackWords c := by unfold LookupStackWords; split <;> decide
      apply backwards_range s.regs.rsp.toBitVec 48 (8*LookupStackWords c) 0 (by omega) a
      obtain ⟨i, hi, eq⟩ := stack
      exact ⟨i, by omega, eq⟩
    · exact .inr (.inl buffer)
  have run := bucket_simulation (outer := s.regs.rsp) fetch agree tracePc traceCmp traceConstCmp c world v entry.projected
    head.machine.data ⟨coverage, preempt, v⟩ (512+preempt) (by
      constructor <;> rw [atHead.stack] <;> stack_not_return) atHead.ready rfl rfl
    head.history [entryPoint s] [] (by simpa only [← atHead.pc] using atHead.related)
    atHead.observed atHead.raw (by rfl) (by rfl) atHead.query atHead.kinds atHead.cursor apart
    [sourceEntry world] atHead.matched atHead.aligned rfl
  have cursor : (⟨⟨head.machine.data, Image.Lookup.entry+0x2f⟩, head.history⟩ : Executed) = head := by
    rw [← atHead.pc]
  rw [cursor] at run
  have run := guarded_prefix head.history ⟨[], by simp⟩ run
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _ _ run
  rintro t ⟨result, prefixed⟩
  exact ⟨head, atHead, prefixed, by simpa only [List.nil_append, CutFrames] using result⟩

#print axioms start_from_entry
#print axioms header_from_started
#print axioms bucket_from_head
end Binary.LookupRelation.First
