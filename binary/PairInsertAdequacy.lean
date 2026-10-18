import PairInsertLoop
import PairInsertPrefix

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels

/-- Executable current-state assertions; the supplied input interpretation and
the random service contracts are separate hypotheses of the theorem. -/
def Pre (n : Names) (o : Offsets) (c : Context) (s : MachineState) (w : World)
    (owner : IndexOwner) (ra : UInt64) (config : RandomProvider.Config) : Prop :=
  callBoundary n o c s w owner ra=.ok () ∧ providerCheck n o c s ra config=.ok ()

def Post (n : Names) (o : Offsets) (c : Context) (initial : MachineState)
    (ra : UInt64) (config : RandomProvider.Config) (inputAt : DataMem → List HiddenRecord → Prop)
    (answer : Nat) (final : World) (t : MachineState) : Prop :=
  Returned initial t ra ∧ t.data.regs.rax.toNat=answer ∧
    MemoryReady c initial ra (savedWords initial.data) .enabled t.data.dmem ∧
    (∃ d, final.k.wg=some d ∧ Corresponds n o t.data.dmem d ∧
      Remove.ownership n o t.data.dmem=.ok (Remove.targetOwnership d)) ∧
    ProviderState config c initial t ∧
    (∃ rest, final.hidden=some rest ∧ inputAt t.data.dmem rest) ∧
    EqualOutside (Writes n o config c initial) initial.data.dmem t.data.dmem ∧
    KindFrame n o initial.data.dmem t.data.dmem

/-- General accepted-return adequacy, covering reinsertion and an arbitrary
finite collision prefix. All later readiness is derived from the entry state
and the preceding execution; no future binary success is an input premise. -/
theorem insert_checked (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) (cmp : TraceCmp4Contract fetch) (bh : BhEnableContract fetch)
    {n o c initial ra config inputAt w owner records answer final}
    (physical : RandomReturnContract fetch config)
    (coupling : RandomInputCoupling fetch config c.coverage (c.preempt+512) (codeEntry+0x79).toUInt64 inputAt)
    (pre : Pre n o c initial w owner ra config)
    (supplied : w.hidden=some records) (input : inputAt initial.data.dmem records)
    (accepted : (WG.indexInsert owner).run w=.ok (answer,final)) :
    Eventually (instructionStep fetch) (Post n o c initial ra config inputAt answer final) initial := by
  obtain ⟨d,base,device,related,storage,owned,resident,pc,table,argument,facts⟩ := boundary_data pre.1
  have provider := providerCheck_sound pre.2
  obtain ⟨rest,path,remaining,finalDevice⟩ := Source.source_input_effect device supplied accepted
  have entryPc : initial.pc=codeEntry := by
    apply Int64.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    exact pc
  have enter := retry_entry fetch decoder trace bh facts related storage owned resident argument entryPc
  have enter := (ProviderState.initial provider).follow fetch enter
    (fun _ post => provider.private_frame post.2.1)
  apply eventually_trans (instructionStep fetch) _ _ _ enter
  rintro unlinked ⟨⟨⟨pc,core,ready⟩,frame,kinds⟩,state⟩
  have input : inputAt unlinked.data.dmem records :=
    coupling.frame _ _ records (provider.private_frame frame) input
  have loop := retry_loop fetch decoder trace cmp bh physical coupling facts provider storage table argument
    path core ready (state.at_pc 0) input
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (at_pc pc loop)
  rintro t ⟨⟨returned,result,memory,related,owned⟩,state,input,outside,kindFrame⟩
  refine ⟨returned,result,memory,⟨_,finalDevice,related,owned⟩,state,⟨rest,remaining,input⟩,
    ?_,kinds.trans kindFrame⟩
  exact fun a no => (ordinary_frame frame a no).trans (outside a no)

#print axioms insert_checked
end Binary.Pair.Insert
