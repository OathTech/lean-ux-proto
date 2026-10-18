import PairInsertWalkNode

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

def walkStart (locked : Bool) (nodes : Nodes) : Int64 :=
  if BitVec.ofNat 64 (Index.head nodes)=0 then walkPC locked 0xc7 else walkPC locked 0x8d

def walkEnd (locked : Bool) (query : Nat) (nodes : Nodes) : Int64 :=
  if nodes.any (fun node => node.2.index==query) then collisionPC locked else walkPC locked 0xcc

/-- Both compiled bucket walks terminate on the finite chain reconstructed
from memory. No bound on the bucket length is supplied to execution. The
loop preserves the same storage relation and callback resources. -/
theorem walk_chain (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) (cmp : TraceCmp4Contract fetch)
    {n o c initial ra p shadow s b previous nodes query}
    (facts : FrameFacts n o c initial ra) (core : Core n o c initial ra p shadow s)
    (validated : n.validate o=.ok ()) (locked : Bool) (registers : WalkRegisters locked query s)
    (small : query<2^32) (shape : Chain n o shadow b previous nodes)
    (cursor : s.regs.rbx.toBitVec=BitVec.ofNat 64 (Index.head nodes)) :
    Eventually (instructionStep fetch) (fun t => t.pc=walkEnd locked query nodes ∧
      Core n o c initial ra p shadow t.data ∧ WalkRegisters locked query t.data)
      ⟨s,walkStart locked nodes⟩ := by
  induction shape generalizing s with
  | nil previous =>
    have call := core.callback fetch (walkPC locked WalkTrace.empty.offset) "L_ffffffff810f3100"
      trace (decoder _ _ (walk_trace_fetch locked .empty)) facts
    apply eventually_weaken (instructionStep fetch) _ _ _ _ call
    rintro t ⟨pc,core,_,r13,r14,_⟩
    exact ⟨by cases locked <;> exact pc,core,registers.frame r13 (fun _ => r14)⟩
  | @cons previous link entry rest fields tail ih =>
    have start : walkStart locked ((link,entry)::rest)=walkPC locked 0x8d := by
      exact ite_eq_right (fields.link_nonzero validated)
    rw [start]
    have visit := walk_node fetch decoder trace cmp facts core validated locked registers small fields cursor
    apply eventually_trans (instructionStep fetch) _ _ _ visit
    rintro compared ⟨pc,core,registers,cursor⟩
    by_cases hit : entry.index==query
    · apply Eventually.done
      refine ⟨?_,core,registers⟩
      simpa only [walkEnd,List.any_cons,hit,Bool.true_or,↓reduceIte] using pc
    · have pc' : compared.pc=walkPC locked 0xb9 := by simpa only [hit,Bool.false_eq_true,↓reduceIte] using pc
      have call := core.callback fetch (walkPC locked WalkTrace.mismatch.offset) "L_ffffffff810f3100"
        trace (decoder _ _ (walk_trace_fetch locked .mismatch)) facts
      apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc' call)
      rintro called ⟨pc,core,bx,r13,r14,_⟩
      have pc' : called.pc=walkPC locked 0xbe := by cases locked <;> exact pc
      have registers := registers.frame r13 (fun _ => r14)
      have cursor : called.data.regs.rbx.toBitVec=BitVec.ofNat 64 (link-o.hash) := by rw [bx]; exact cursor
      have nextBound : Index.head rest<2^64 := word_bound fields.forward
      have read : called.data.dmem.loadInt (called.data.regs.rbx.toBitVec+8) 8=
          some (BitVec.ofNat 64 (Index.head rest)).toNat := by
        rw [cursor,BitVec.toNat_ofNat,Nat.mod_eq_of_lt nextBound]
        exact (fields.frame (validate_basic validated).1 core.frame).next_load (validate_basic validated).1
      have advance := walk_advance fetch decoder core locked (.ofNat 64 (Index.head rest)) read
      apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc' advance)
      rintro advanced ⟨pc,core,regs⟩
      have registers : WalkRegisters locked query advanced.data :=
        registers.frame (by rw [regs]) (fun _ => by rw [regs])
      have cursor : advanced.data.regs.rbx.toBitVec=BitVec.ofNat 64 (Index.head rest) := by rw [regs]
      have recurse := ih core registers cursor
      have pc' : advanced.pc=walkStart locked rest := pc
      apply eventually_weaken (instructionStep fetch) _ _ _ _ (at_pc pc' recurse)
      rintro final ⟨pc,core,registers⟩
      refine ⟨?_,core,registers⟩
      simpa only [walkEnd,List.any_cons,show (entry.index==query)=false from Bool.eq_false_iff.mpr hit,
        Bool.false_or] using pc

#print axioms walk_chain
end Binary.Pair.Insert
