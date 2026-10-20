import SourceAdapter
import PairSequenceCall
import PairLookupFirstEnvironment
import PairRemoveFirstEnvironment
import PairReplaceFirstEnvironment
import GuardedMemoryInvariant
namespace Binary.Pair.Sequence.First
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index Callback
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 2048
/-- Derive the chosen function's executable Pre from the retained resources
and source-only admissibility, then preserve the same resources at return. -/
theorem call_checked (fetch : Int64 → Option Decoded)
    (lookupDecoder : AnchoredDecoderAgreement fetch)
    (removeDecoder : IndexRemoveDecoderAgreement fetch)
    (replaceDecoder : IndexReplaceDecoderAgreement fetch)
    (services : ServiceDecoderAgreement fetch)
    {n o c base initialWorld ra current w call answer finalWorld}
    (facts : InitialFacts n o c base initialWorld ra)
    (ready : Ready n o c base current.data.dmem w)
    (admissible : Admissible n call w)
    (accepted : (source call).run w=.ok (answer,finalWorld)) :
    ∃ entry, prepare n base ra call current=.ok entry ∧
      Eventually (guardedStep fetch (StackGuard entry.data.regs.rsp)) (Post n o c base ra current entry answer finalWorld) entry := by
  cases call with
  | lookup query kinds =>
    change ((Source.indexLookup kinds query).run w >>= fun p => .ok (.lookup p.1,p.2))=.ok (answer,finalWorld) at accepted
    obtain ⟨⟨value,world⟩,run,equal⟩ := bind_ok accepted
    have equal : (Answer.lookup value,world)=(answer,finalWorld) := Except.ok.inj equal
    cases equal
    let entry := install n base ra Image.Lookup.entry (kindMask kinds) query current
    have prepared := install_ready facts ready Image.Lookup.entry (kindMask kinds) query
    refine ⟨entry,rfl,?_⟩
    have executed := IndexLookup.First.lookup_checked fetch lookupDecoder (pc_leaf fetch services) (cmp4_leaf fetch services) (const_cmp4_leaf fetch services) (const_cmp1_leaf fetch services) (bh_leaf fetch services)
      (lookup_pre facts ready admissible) run
    apply eventually_weaken (guardedStep fetch (StackGuard entry.data.regs.rsp)) _ _ _ _ (guarded_mapped fetch executed)
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
    · have executed := Remove.First.remove_checked fetch removeDecoder (pc_guarded fetch services) (bh_guarded fetch services) (remove_pre facts ready named) run
      apply eventually_weaken (guardedStep fetch (StackGuard entry.data.regs.rsp)) _ _ _ _ (guarded_mapped fetch executed)
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
    · have executed := Replace.First.replace_checked fetch replaceDecoder (pc_guarded fetch services) (bh_guarded fetch services)
        (replace_pre facts ready oldAddress newAddress fresh) run
      apply eventually_weaken (guardedStep fetch (StackGuard entry.data.regs.rsp)) _ _ _ _ (guarded_mapped fetch executed)
      rintro final ⟨⟨returned,result,memory,state,frame,kindsFrame⟩,mapped⟩
      exact ⟨⟨returned,result⟩,⟨state,memory.covered,memory.preempt,memory.pending,
        (fun a size prior => mapped a size (prepared.mapped a size prior)),prepared.kinds.trans kindsFrame⟩,
        mutator_frame (by omega : 5≤13) frame⟩

#print axioms call_checked
end Binary.Pair.Sequence.First
