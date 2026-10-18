import PairInsertWalkData
import PairInsertWalkBranches

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

structure WalkRegisters (locked : Bool) (query : Nat) (s : MachineData) : Prop where
  value : s.regs.r13.toNat=query
  bucket : locked=true → s.regs.r14.toNat=query%8192

theorem WalkRegisters.frame {locked query s t} (regs : WalkRegisters locked query s)
    (r13 : t.regs.r13=s.regs.r13) (r14 : locked=true → t.regs.r14=s.regs.r14) :
    WalkRegisters locked query t :=
  ⟨by rw [r13]; exact regs.value,fun h => by rw [r14 h]; exact regs.bucket h⟩

theorem WalkRegisters.same {locked query s t} (regs : WalkRegisters locked query s)
    (same : t.regs=s.regs) : WalkRegisters locked query t :=
  regs.frame (by rw [same]) (fun _ => by rw [same])

theorem query_low (s : MachineData) :
    (s.regs.get (.low .r13 .W32)).toNat=s.regs.r13.toNat%2^32 := by
  simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop]

theorem compared_low (locked : Bool) (s : MachineData) :
    comparedIndex locked s=(if locked then s.regs.r15.toNat else s.regs.r14.toNat)%2^32 := by
  cases locked <;> simp [comparedIndex,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop]

/-- One nonempty walk iteration through its comparison. The two walks use
the same proof; only code locations and the compared-value register differ. -/
theorem walk_node (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) (cmp : TraceCmp4Contract fetch)
    {n o c initial ra p shadow s b link previous next entry query}
    (facts : FrameFacts n o c initial ra) (core : Core n o c initial ra p shadow s)
    (validated : n.validate o=.ok ()) (locked : Bool) (registers : WalkRegisters locked query s)
    (small : query<2^32) (fields : NodeFields n o shadow b link previous next entry)
    (cursor : s.regs.rbx.toBitVec=BitVec.ofNat 64 link) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=(if entry.index==query then collisionPC locked else walkPC locked 0xb9) ∧
      Core n o c initial ra p shadow t.data ∧ WalkRegisters locked query t.data ∧
      t.data.regs.rbx.toBitVec=BitVec.ofNat 64 (link-o.hash)) ⟨s,walkPC locked 0x8d⟩ := by
  have layout := (validate_basic validated).1
  have first := core.callback fetch (walkPC locked WalkTrace.entry.offset) "L_ffffffff810f3100"
    trace (decoder _ _ (walk_trace_fetch locked .entry)) facts
  apply eventually_trans (instructionStep fetch) _ _ _ first
  rintro called ⟨pc,core,bx,r13,r14,_⟩
  have pc' : called.pc=walkPC locked 0x92 := by cases locked <;> exact pc
  have registers := registers.frame r13 (fun _ => r14)
  have cursor : called.data.regs.rbx.toBitVec=BitVec.ofNat 64 link := by rw [bx]; exact cursor
  have adjust := walk_cursor fetch decoder trace facts core locked
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc' adjust)
  rintro adjusted ⟨pc,core,bx,r13,r14,_⟩
  have registers := registers.frame r13 (fun _ => r14)
  have cursor : adjusted.data.regs.rbx.toBitVec=BitVec.ofNat 64 (link-o.hash) := by
    rw [bx,UInt64.toBitVec_sub,cursor]
    have expanded : BitVec.ofNat 64 link=BitVec.ofNat 64 (link-o.hash)+8 := by
      calc
        BitVec.ofNat 64 link=BitVec.ofNat 64 ((link-o.hash)+8) := by
          congr 1
          have valid := fields.valid
          rw [layout.hash] at valid ⊢
          omega
        _=BitVec.ofNat 64 (link-o.hash)+8 := by rw [BitVec.ofNat_add]; rfl
    rw [expanded]
    change (BitVec.ofNat 64 (link-o.hash)+8)-8=BitVec.ofNat 64 (link-o.hash)
    exact BitVec.add_sub_cancel _ _
  have guard := walk_guard fetch decoder core locked (by rw [cursor]; exact fields.base_nonzero validated)
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc guard)
  rintro guarded ⟨pc,core,regs⟩
  have registers := registers.same regs
  have cursor : guarded.data.regs.rbx.toBitVec=BitVec.ofNat 64 (link-o.hash) := by rw [regs]; exact cursor
  have visit := core.callback fetch (walkPC locked WalkTrace.present.offset) "L_ffffffff810f3100"
    trace (decoder _ _ (walk_trace_fetch locked .present)) facts
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc visit)
  rintro visited ⟨pc,core,bx,r13,r14,_⟩
  have pc' : visited.pc=walkPC locked 0xa5 := by cases locked <;> exact pc
  have registers := registers.frame r13 (fun _ => r14)
  have cursor : visited.data.regs.rbx.toBitVec=BitVec.ofNat 64 (link-o.hash) := by rw [bx]; exact cursor
  have indexBound : entry.index<2^32 := word_bound fields.index
  have indexValue : (UInt32.ofNat entry.index).toNat=entry.index := by
    change entry.index%2^32=entry.index
    exact Nat.mod_eq_of_lt indexBound
  have read : visited.data.dmem.loadInt (visited.data.regs.rbx.toBitVec+28) 4=
      some (UInt32.ofNat entry.index).toNat := by
    rw [cursor,indexValue]
    exact (fields.frame layout core.frame).index_load layout
  have arguments := walk_arguments fetch decoder cmp facts core locked (.ofNat entry.index) read
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc' arguments)
  rintro compared ⟨pc,core,bx,r13,r14,r15⟩
  have nextRegisters := registers.frame r13 (fun active => by subst locked; exact r14)
  have cursor : compared.data.regs.rbx.toBitVec=BitVec.ofNat 64 (link-o.hash) := by rw [bx]; exact cursor
  have equalIndex : comparedIndex locked compared.data=entry.index := by
    rw [compared_low]
    cases locked with
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte,r14,argumentRegisters]
      rw [indexValue]
      change (entry.index%2^64)%2^32=entry.index
      rw [Nat.mod_eq_of_lt (by omega : entry.index<2^64),Nat.mod_eq_of_lt indexBound]
    | true =>
      simp only [↓reduceIte,r15,argumentRegisters]
      rw [indexValue]
      change (entry.index%2^64)%2^32=entry.index
      rw [Nat.mod_eq_of_lt (by omega : entry.index<2^64),Nat.mod_eq_of_lt indexBound]
  have comparison := walk_compare fetch decoder core locked
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (at_pc pc comparison)
  rintro final ⟨pc,core,regs⟩
  refine ⟨?_,core,nextRegisters.same regs,by rw [regs]; exact cursor⟩
  rw [query_low,nextRegisters.value,Nat.mod_eq_of_lt small,equalIndex] at pc
  have symmetric : (query==entry.index)=(entry.index==query) := by
    by_cases equal : query=entry.index
    · subst query; rfl
    · simp only [beq_eq_false_iff_ne.mpr equal,beq_eq_false_iff_ne.mpr (Ne.symm equal)]
  simpa only [symmetric] using pc

#print axioms walk_node
end Binary.Pair.Insert
