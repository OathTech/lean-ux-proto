import PairInsertAttempt
import PairInsertSourceInput

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

def LoopPost (n : Names) (o : Offsets) (c : Context) (initial : MachineState)
    (ra : UInt64) (config : RandomProvider.Config) (inputAt : DataMem → List HiddenRecord → Prop)
    (before : DataMem) (d : Device) (owner : IndexOwner) (value : Nat)
    (rest : List HiddenRecord) (t : MachineState) : Prop :=
  Completed n o c initial ra d owner value t ∧ ProviderState config c initial t ∧
    inputAt t.data.dmem rest ∧ EqualOutside (Writes n o config c initial) before t.data.dmem ∧
    KindFrame n o before t.data.dmem

/-- Arbitrary finite accepted collision prefixes. The induction is on the
actual source input protocol, with no independent bound on binary retries. -/
theorem retry_loop (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) (cmp : TraceCmp4Contract fetch) (bh : BhEnableContract fetch)
    {n o c initial ra config inputAt s d owner base records value rest}
    (physical : RandomReturnContract fetch config)
    (coupling : RandomInputCoupling fetch config c.coverage (c.preempt+512) (codeEntry+0x79).toUInt64 inputAt)
    (facts : FrameFacts n o c initial ra) (provider : ProviderFacts n o c initial ra config)
    (storage : storageCheck n o=true) (table : initial.data.regs.rdi.toNat=n.table)
    (argument : initial.data.regs.rsi.toNat=base)
    (path : Source.DrawSearch d.indexTable records value rest)
    (core : Core n o c initial ra .outer s.dmem s)
    (ready : RetryData n o s.dmem d owner base) (state : ProviderState config c initial ⟨s,0⟩)
    (input : inputAt s.dmem records) :
    Eventually (instructionStep fetch)
      (LoopPost n o c initial ra config inputAt s.dmem d owner value rest) ⟨s,codeEntry+0x6f⟩ := by
  induction path generalizing s with
  | fresh decoded miss =>
    have one := attempt fetch decoder trace cmp bh physical coupling facts provider
      core ready state storage table argument input decoded
    apply eventually_weaken (instructionStep fetch) _ _ _ _ one
    rintro t ⟨outcome,state,input,frame,kinds⟩
    refine ⟨?_,state,input,frame,kinds⟩
    simpa only [AttemptOutcome,miss,Bool.false_eq_true,↓reduceIte] using outcome
  | collision decoded hit tail ih =>
    have one := attempt fetch decoder trace cmp bh physical coupling facts provider
      core ready state storage table argument input decoded
    apply eventually_trans (instructionStep fetch) _ _ _ one
    rintro retried ⟨outcome,state,input,frame,kinds⟩
    have retry : RetryPost n o c initial ra d owner base retried := by
      simpa only [AttemptOutcome,hit,↓reduceIte] using outcome
    have loop := ih retry.2.1 retry.2.2 (state.at_pc 0) input
    apply eventually_weaken (instructionStep fetch) _ _ _ _ (at_pc retry.1 loop)
    rintro t ⟨completed,state,input,remaining,kindFrame⟩
    refine ⟨completed,state,input,?_,kinds.trans kindFrame⟩
    exact fun a no => (frame a no).trans (remaining a no)

#print axioms retry_loop
end Binary.Pair.Insert
