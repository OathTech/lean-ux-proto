import PairInsertNested
import PairInsertDrawEntry
import PairInsertSourceBucket

namespace Binary.Pair.Index
open Leanux Leanux.WG

theorem InsertFocus.collision {n o m d} (f : InsertFocus n o m) (related : Corresponds n o m d) :
    f.nodes.any (fun node => node.2.index==f.index)=d.indexTable.any (·.index==f.index) := by
  have same := Except.ok.inj (f.original_bucket.symm.trans
    (reconstruct_bucket related (Nat.mod_lt f.index (by decide))))
  have mapped : f.nodes.any (fun node => node.2.index==f.index)=
      (f.nodes.map Prod.snd).any (·.index==f.index) := by simp only [List.any_map]; rfl
  rw [mapped,same,Insert.Source.bucket_any]

end Binary.Pair.Index

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

/-- In the sequential environment, the locked recheck reads the very same
chain as the first miss. Its miss is derived, not an extra assumed outcome. -/
theorem recheck_miss (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) (cmp : TraceCmp4Contract fetch)
    {n o c initial ra shadow s} (facts : FrameFacts n o c initial ra)
    (core : Core n o c initial ra .outer shadow s) (validated : n.validate o=.ok ())
    (focus : InsertFocus n o shadow)
    (table : initial.data.regs.rdi.toNat=n.table) (owner : initial.data.regs.rsi.toNat=focus.fresh.base)
    (miss : focus.nodes.any (fun node => node.2.index==focus.index)=false) :
    Eventually (instructionStep fetch) (fun t => t.pc=codeEntry+0x136 ∧
      Core n o c initial ra .inner shadow t.data ∧ WalkRegisters true focus.index t.data)
      ⟨s,walkPC false 0xcc⟩ := by
  have call := core.callback fetch (walkPC false WalkTrace.finish.offset) "L_ffffffff810f3100"
    trace (decoder _ _ (walk_trace_fetch false .finish)) facts
  apply eventually_trans (instructionStep fetch) _ _ _ call
  rintro called ⟨pc,core,_,_,_,_⟩
  have pc' : called.pc=codeEntry+0xd1 := pc
  have enter := nested_entry fetch decoder facts core (validate_basic validated).1 focus table owner
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc' enter)
  rintro entered ⟨pc,core,registers,cursor⟩
  have walk := walk_chain fetch decoder trace cmp facts core validated true registers
    (word_bound focus.indexRead) focus.shape cursor
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc walk)
  rintro walked ⟨pc,core,registers⟩
  have pc' : walked.pc=walkPC true 0xcc := by simpa only [walkEnd,miss,Bool.false_eq_true,↓reduceIte] using pc
  have call := core.callback fetch (walkPC true WalkTrace.finish.offset) "L_ffffffff810f3100"
    trace (decoder _ _ (walk_trace_fetch true .finish)) facts
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (at_pc pc' call)
  rintro final ⟨pc,core,_,r13,r14,_⟩
  exact ⟨pc,core,registers.frame r13 (fun _ => r14)⟩

def SearchPost (n : Names) (o : Offsets) (c : Context) (initial : MachineState)
    (ra : UInt64) (shadow : DataMem) (focus : InsertFocus n o shadow) (t : MachineState) : Prop :=
  if focus.nodes.any (fun node => node.2.index==focus.index) then
    t.pc=codeEntry+0x6f ∧ Core n o c initial ra .outer shadow t.data
  else t.pc=codeEntry+0x136 ∧ Core n o c initial ra .inner shadow t.data ∧ WalkRegisters true focus.index t.data

theorem search (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) (cmp : TraceCmp4Contract fetch)
    {n o c initial ra shadow s} (facts : FrameFacts n o c initial ra)
    (core : Core n o c initial ra .outer shadow s) (validated : n.validate o=.ok ())
    (focus : InsertFocus n o shadow)
    (table : initial.data.regs.rdi.toNat=n.table) (owner : initial.data.regs.rsi.toNat=focus.fresh.base)
    (registers : WalkRegisters false focus.index s)
    (cursor : s.regs.rbx.toBitVec=BitVec.ofNat 64 (Index.head focus.nodes)) :
    Eventually (instructionStep fetch) (SearchPost n o c initial ra shadow focus) ⟨s,walkStart false focus.nodes⟩ := by
  have walk := walk_chain fetch decoder trace cmp facts core validated false registers
    (word_bound focus.indexRead) focus.shape cursor
  apply eventually_trans (instructionStep fetch) _ _ _ walk
  rintro walked ⟨pc,core,_⟩
  cases outcome : focus.nodes.any (fun node => node.2.index==focus.index) with
  | true =>
    apply Eventually.done
    unfold SearchPost
    rw [outcome]
    refine ⟨?_,core⟩
    simpa only [walkEnd,outcome,collisionPC,Bool.false_eq_true,↓reduceIte] using pc
  | false =>
    have pc' : walked.pc=walkPC false 0xcc := by simpa only [walkEnd,outcome,Bool.false_eq_true,↓reduceIte] using pc
    apply eventually_weaken (instructionStep fetch) _ _ _ _
      (at_pc pc' (recheck_miss fetch decoder trace cmp facts core validated focus table owner outcome))
    intro t post
    unfold SearchPost
    rw [outcome]
    exact post

#print axioms recheck_miss
#print axioms search
end Binary.Pair.Insert
