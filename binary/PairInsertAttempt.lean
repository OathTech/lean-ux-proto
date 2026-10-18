import PairInsertRetryDraw
import PairInsertSearch
import PairInsertSuccess

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

def Completed (n : Names) (o : Offsets) (c : Context) (initial : MachineState)
    (ra : UInt64) (d : Device) (owner : IndexOwner) (value : Nat) (t : MachineState) : Prop :=
  Returned initial t ra ∧ t.data.regs.rax.toNat=value ∧
    MemoryReady c initial ra (savedWords initial.data) .enabled t.data.dmem ∧
    Corresponds n o t.data.dmem {d with indexTable := ⟨value,owner⟩::d.indexTable} ∧
    Remove.ownership n o t.data.dmem=.ok
      (Remove.targetOwnership {d with indexTable := ⟨value,owner⟩::d.indexTable})

def AttemptOutcome (n : Names) (o : Offsets) (c : Context) (initial : MachineState)
    (ra : UInt64) (d : Device) (owner : IndexOwner) (base value : Nat) (t : MachineState) : Prop :=
  if d.indexTable.any (·.index==value) then RetryPost n o c initial ra d owner base t
  else Completed n o c initial ra d owner value t

/-- Everything after the random return is ordinary execution. The locked
second scan's result is derived by `search` from the same unchanged chain. -/
theorem draw_attempt (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) (cmp : TraceCmp4Contract fetch) (bh : BhEnableContract fetch)
    {n o c initial ra s d owner base value}
    (facts : FrameFacts n o c initial ra) (core : Core n o c initial ra .outer s.dmem s)
    (ready : RetryData n o s.dmem d owner base) (storage : storageCheck n o=true)
    (table : initial.data.regs.rdi.toNat=n.table) (argument : initial.data.regs.rsi.toNat=base)
    (valueEq : (drawWord s).toNat=value) :
    Eventually (instructionStep fetch) (fun t => AttemptOutcome n o c initial ra d owner base value t ∧
      EqualOutside (fun a => HeapBytes n o a ∨ External c initial 7 a) s.dmem t.data.dmem ∧
      KindFrame n o s.dmem t.data.dmem) ⟨s,codeEntry+0x79⟩ := by
  have validated := (reconstruct_components ready.related).1
  have layout := (validate_basic validated).1
  obtain ⟨focus,ownerEq,baseEq,indexEq,drawReady,enter⟩ :=
    draw_entry fetch decoder facts core ready storage table argument
  have chosen : focus.index=value := indexEq.trans valueEq
  have heapFrame := ready.entry.draw_heap_frame (drawWord s).toNat layout
  have kinds := ready.entry.draw_kind_frame (drawWord s).toNat layout storage
  have hit : focus.nodes.any (fun node => node.2.index==focus.index)=
      d.indexTable.any (·.index==value) := by rw [focus.collision drawReady.related,chosen]
  apply eventually_trans (instructionStep fetch) _ _ _ enter
  rintro entered ⟨pc,core,registers,cursor⟩
  have scan := search fetch decoder trace cmp facts core validated focus table
    (argument.trans baseEq.symm) registers cursor
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc scan)
  intro scanned scannedPost
  cases outcome : d.indexTable.any (·.index==value) with
  | true =>
    have post : scanned.pc=codeEntry+0x6f ∧
        Core n o c initial ra .outer (ready.entry.afterDraw (drawWord s).toNat) scanned.data := by
      simpa only [SearchPost,hit,outcome,↓reduceIte] using scannedPost
    apply Eventually.done
    refine ⟨?_,?_,kinds.trans (post.2.frame.kinds layout)⟩
    · simpa only [AttemptOutcome,outcome,↓reduceIte] using
        (show RetryPost n o c initial ra d owner base scanned from
          ⟨post.1,post.2.rebase,drawReady.frame post.2.frame⟩)
    · intro a outside
      exact (heapFrame a (fun h => outside (.inl h))).trans
        (post.2.outside a (fun h => outside (.inr h)))
  | false =>
    have post : scanned.pc=codeEntry+0x136 ∧
        Core n o c initial ra .inner (ready.entry.afterDraw (drawWord s).toNat) scanned.data ∧
        WalkRegisters true focus.index scanned.data := by
      simpa only [SearchPost,hit,outcome,Bool.false_eq_true,↓reduceIte] using scannedPost
    have focusReady : RetryData n o (ready.entry.afterDraw (drawWord s).toNat) d
        focus.fresh.owner focus.fresh.base := by simpa only [ownerEq,baseEq] using drawReady
    have finish := insert_success fetch decoder trace bh facts post.2.1 focus focusReady
      storage table (argument.trans baseEq.symm) post.2.2
    apply eventually_weaken (instructionStep fetch) _ _ _ _ (at_pc post.1 finish)
    rintro t ⟨returned,result,memory,related,owned,outside,kindFrame⟩
    refine ⟨?_,?_,kinds.trans kindFrame⟩
    · simp only [AttemptOutcome,outcome,Bool.false_eq_true,↓reduceIte,Completed]
      refine ⟨returned,result.trans chosen,memory,?_,?_⟩
      · simpa only [chosen,ownerEq] using related
      · simpa only [chosen,ownerEq] using owned
    · intro a no
      exact (heapFrame a (fun h => no (.inl h))).trans (outside a no)

/-- One complete attempt, with current physical provider readiness and exact
ordered input consumption. Collision returns to the same executable invariant. -/
theorem attempt (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) (cmp : TraceCmp4Contract fetch) (bh : BhEnableContract fetch)
    {n o c initial ra config inputAt s d owner base records value rest}
    (physical : RandomReturnContract fetch config)
    (coupling : RandomInputCoupling fetch config c.coverage (c.preempt+512) (codeEntry+0x79).toUInt64 inputAt)
    (facts : FrameFacts n o c initial ra) (provider : ProviderFacts n o c initial ra config)
    (core : Core n o c initial ra .outer s.dmem s)
    (ready : RetryData n o s.dmem d owner base) (state : ProviderState config c initial ⟨s,0⟩)
    (storage : storageCheck n o=true) (table : initial.data.regs.rdi.toNat=n.table)
    (argument : initial.data.regs.rsi.toNat=base)
    (input : inputAt s.dmem records) (decoded : draw records=.ok (value,rest)) :
    Eventually (instructionStep fetch) (fun t => AttemptOutcome n o c initial ra d owner base value t ∧
      ProviderState config c initial t ∧ inputAt t.data.dmem rest ∧
      EqualOutside (Writes n o config c initial) s.dmem t.data.dmem ∧
      KindFrame n o s.dmem t.data.dmem) ⟨s,codeEntry+0x6f⟩ := by
  have random := retry_draw fetch decoder trace physical coupling facts provider core ready state input decoded
  apply eventually_trans (instructionStep fetch) _ _ _ random
  rintro drawn ⟨pc,core,ready,state,input,valueEq,outside,kinds⟩
  have body := draw_attempt fetch decoder trace cmp bh facts core ready storage table argument valueEq
  have body := (state.at_pc (codeEntry+0x79)).follow fetch body
    (fun _ post => provider.private_frame post.2.1)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (at_pc pc body)
  rintro t ⟨⟨outcome,frame,kindFrame⟩,state⟩
  refine ⟨outcome,state,coupling.frame _ _ rest (provider.private_frame frame) input,
    ?_,kinds.trans kindFrame⟩
  intro a no
  exact (outside a no).trans (ordinary_frame frame a no)

#print axioms draw_attempt
#print axioms attempt
end Binary.Pair.Insert
