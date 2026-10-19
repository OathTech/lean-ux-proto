import SourceAdapter
import PairSequenceFrame

namespace Binary.Pair.Sequence
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 2048

def Post (n : Names) (o : Offsets) (c : Context) (base : MachineState) (ra : UInt64)
    (current entry : MachineState) (answer : Answer) (w : World) (final : MachineState) : Prop :=
  Interface n ra entry final answer ∧ Ready n o c base final.data.dmem w ∧
    EqualOutside (Writes n o c base) current.data.dmem final.data.dmem

/-- Derive the chosen function's executable Pre from the retained resources
and source-only admissibility, then preserve the same resources at return. -/
theorem call_checked (fetch : Int64 → Option Decoded)
    (lookupDecoder : AnchoredDecoderAgreement fetch)
    (removeDecoder : IndexRemoveDecoderAgreement fetch)
    (replaceDecoder : IndexReplaceDecoderAgreement fetch)
    (trace : TracePcContract fetch) (cmp : TraceCmp4Contract fetch)
    (constCmp : TraceConstCmp4Contract fetch) (byte : TraceConstCmp1Contract fetch)
    (bh : BhEnableContract fetch)
    {n o c base initialWorld ra current w call answer finalWorld}
    (facts : InitialFacts n o c base initialWorld ra)
    (ready : Ready n o c base current.data.dmem w)
    (admissible : Admissible n call w)
    (accepted : (source call).run w=.ok (answer,finalWorld)) :
    ∃ entry, prepare n base ra call current=.ok entry ∧
      Eventually (instructionStep fetch) (Post n o c base ra current entry answer finalWorld) entry := by
  cases call with
  | lookup query kinds =>
    change ((Source.indexLookup kinds query).run w >>= fun p => .ok (.lookup p.1,p.2))=.ok (answer,finalWorld) at accepted
    obtain ⟨⟨value,world⟩,run,equal⟩ := bind_ok accepted
    have equal : (Answer.lookup value,world)=(answer,finalWorld) := Except.ok.inj equal
    cases equal
    let entry := install n base ra Image.Lookup.entry (kindMask kinds) query current
    have prepared := install_ready facts ready Image.Lookup.entry (kindMask kinds) query
    refine ⟨entry,rfl,?_⟩
    have executed := IndexLookup.lookup_checked fetch lookupDecoder trace cmp constCmp byte bh
      (lookup_pre facts ready admissible) run
    apply eventually_weaken (instructionStep fetch) _ _ _ _ (MemoryInvariant.eventually_mapped fetch executed)
    rintro final ⟨⟨returned,result,state,coverage,preempt,pending,frame,kindsFrame⟩,mapped⟩
    exact ⟨⟨returned,result⟩,⟨state,coverage,preempt,pending,
      (fun a size prior => mapped a size (prepared.mapped a size prior)),prepared.kinds.trans kindsFrame⟩,
      lookup_frame frame⟩
  | remove owner =>
    obtain ⟨address,named⟩ := admissible
    change ((Source.indexRemove owner).run w >>= fun p => .ok (.remove,p.2))=.ok (answer,finalWorld) at accepted
    obtain ⟨⟨value,world⟩,run,equal⟩ := bind_ok accepted
    cases value
    have equal : (Answer.remove,world)=(answer,finalWorld) := Except.ok.inj equal
    cases equal
    let entry := install n base ra (.ofNat Remove.entry) address 0 current
    have prepared := install_ready facts ready (.ofNat Remove.entry) address 0
    refine ⟨entry,?_,?_⟩
    · simp only [prepare,named]; rfl
    · have executed := Remove.remove_checked fetch removeDecoder trace bh (remove_pre facts ready named) run
      apply eventually_weaken (instructionStep fetch) _ _ _ _ (MemoryInvariant.eventually_mapped fetch executed)
      rintro final ⟨⟨returned,memory,state,frame,kindsFrame⟩,mapped⟩
      exact ⟨⟨returned,True.intro⟩,⟨state,memory.covered,memory.preempt,memory.pending,
        (fun a size prior => mapped a size (prepared.mapped a size prior)),prepared.kinds.trans kindsFrame⟩,
        mutator_frame (by omega : 4≤13) frame⟩
  | replace pid kid =>
    obtain ⟨⟨old,oldAddress⟩,⟨new,newAddress⟩,fresh⟩ := admissible
    change ((Source.indexReplaceHandshake pid kid).run w >>= fun p => .ok (.replace p.1,p.2))=.ok (answer,finalWorld) at accepted
    obtain ⟨⟨value,world⟩,run,equal⟩ := bind_ok accepted
    have equal : (Answer.replace value,world)=(answer,finalWorld) := Except.ok.inj equal
    cases equal
    let entry := install n base ra (.ofNat Replace.entry) old new current
    have prepared := install_ready facts ready (.ofNat Replace.entry) old new
    refine ⟨entry,?_,?_⟩
    · simp only [prepare,oldAddress,newAddress]; rfl
    · have executed := Replace.replace_checked fetch replaceDecoder trace bh
        (replace_pre facts ready oldAddress newAddress fresh) run
      apply eventually_weaken (instructionStep fetch) _ _ _ _ (MemoryInvariant.eventually_mapped fetch executed)
      rintro final ⟨⟨returned,result,memory,state,frame,kindsFrame⟩,mapped⟩
      exact ⟨⟨returned,result⟩,⟨state,memory.covered,memory.preempt,memory.pending,
        (fun a size prior => mapped a size (prepared.mapped a size prior)),prepared.kinds.trans kindsFrame⟩,
        mutator_frame (by omega : 5≤13) frame⟩

#print axioms call_checked
end Binary.Pair.Sequence
