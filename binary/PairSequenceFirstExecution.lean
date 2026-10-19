import PairSequenceExecution
import PairSequenceFirstCall
namespace Binary.Pair.Sequence.First
open Leanux Leanux.WG TrustBase Callback
local instance : Labels := Image.linkedLabels
theorem call_history (fetch : Int64 → Option Decoded)
    (lookupDecoder : AnchoredDecoderAgreement fetch)
    (removeDecoder : IndexRemoveDecoderAgreement fetch)
    (replaceDecoder : IndexReplaceDecoderAgreement fetch)
    (services : ServiceDecoderAgreement fetch) (permissions : Permissions) (onlineCPUs : Nat) (externalActions : List Nat)
    {n o c base initialWorld ra current w call answer finalWorld}
    (environment : SerializedEnvironment onlineCPUs externalActions)
    (access : FirstReturnDomainPermissions fetch permissions ra (EntryDomain n base ra))
    (facts : InitialFacts n o c base initialWorld ra) (ready : Ready n o c base current.data.dmem w)
    (admissible : Admissible n call w) (accepted : (source call).run w=.ok (answer,finalWorld)) :
    ∃ entry, prepare n base ra call current=.ok entry ∧
      Eventually (historyStep fetch) (fun final =>
        Observed fetch permissions onlineCPUs externalActions n ra answer (entry,final) ∧
        BeforeOuterReturn entry ra final.history ∧
        Ready n o c base final.machine.data.dmem finalWorld ∧
        EqualOutside (Writes n o c base) current.data.dmem final.machine.data.dmem) ⟨entry,[entry]⟩ := by
  obtain ⟨entry,prepared,physical⟩ := call_checked fetch lookupDecoder removeDecoder replaceDecoder
    services facts ready admissible accepted
  refine ⟨entry,prepared,?_⟩
  have history := guarded_history fetch _ _ entry physical [] (by simp)
  have actual := eventually_actual fetch entry _ _ history .start (by simp)
  have last := history_last fetch _ _ (by simp) actual
  apply eventually_weaken (historyStep fetch) _ _ _ _ last
  rintro t ⟨⟨⟨⟨interface,ready,frame⟩,interior⟩,actual⟩,last⟩
  have first : BeforeOuterReturn entry ra t.history := by
    intro q member boundary
    exact interior q member boundary.2
  exact ⟨⟨interface,actual,last,environment,
    access entry ⟨call,current,prepared⟩ t.history actual first⟩,first,ready,frame⟩

#print axioms call_history
end Binary.Pair.Sequence.First
