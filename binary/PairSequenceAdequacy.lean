import PairSequenceExecution

namespace Binary.Pair.Sequence
open Leanux Leanux.WG TrustBase
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 2048

/-- Caller obligations evaluated only along accepted source prefixes.
There is no binary state, future Pre or future successful execution here. -/
def AdmissibleSequence (n : Names) : List Call → World → Prop
  | [],_ => True
  | call::rest,w => Admissible n call w ∧ ∀ answer next,
      (source call).run w=.ok (answer,next) → AdmissibleSequence n rest next

def SequencePost (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (onlineCPUs : Nat) (externalActions : List Nat) (n : Names) (o : Offsets)
    (c : CommonBitsCoverage.Context) (base current : MachineState) (ra : UInt64)
    (answers : List Answer) (finalWorld : World) (records : List CallRecord) (final : MachineState) : Prop :=
  Ready n o c base final.data.dmem finalWorld ∧
    Mapped (Observed fetch permissions onlineCPUs externalActions n ra) answers records ∧
    EqualOutside (Writes n o c base) current.data.dmem final.data.dmem

theorem sequence_from_ready (fetch : Int64 → Option Decoded)
    (lookupDecoder : AnchoredDecoderAgreement fetch)
    (removeDecoder : IndexRemoveDecoderAgreement fetch)
    (replaceDecoder : IndexReplaceDecoderAgreement fetch)
    (trace : TracePcContract fetch) (cmp : TraceCmp4Contract fetch)
    (constCmp : TraceConstCmp4Contract fetch) (byte : TraceConstCmp1Contract fetch)
    (bh : BhEnableContract fetch) (permissions : Permissions) (onlineCPUs : Nat) (externalActions : List Nat)
    {n o c base initialWorld ra current w calls answers finalWorld}
    (environment : SerializedEnvironment onlineCPUs externalActions)
    (access : ReturningDomainPermissions fetch permissions ra (EntryDomain n base ra))
    (facts : InitialFacts n o c base initialWorld ra)
    (ready : Ready n o c base current.data.dmem w)
    (admissible : AdmissibleSequence n calls w)
    (accepted : (program calls).run w=.ok (answers,finalWorld)) :
    Execute fetch n base ra calls current
      (SequencePost fetch permissions onlineCPUs externalActions n o c base current ra answers finalWorld) := by
  induction calls generalizing current w answers finalWorld with
  | nil =>
    change Except.ok ([],w)=Except.ok (answers,finalWorld) at accepted
    cases Except.ok.inj accepted
    exact ⟨ready,.nil,fun _ _ => rfl⟩
  | cons call rest ih =>
    change ((source call).run w >>= fun p => (program rest).run p.2 >>= fun q =>
      .ok (p.1::q.1,q.2))=.ok (answers,finalWorld) at accepted
    obtain ⟨⟨answer,middle⟩,first,accepted⟩ := bind_ok accepted
    obtain ⟨⟨remaining,lastWorld⟩,later,accepted⟩ := bind_ok accepted
    have equal : (answer::remaining,lastWorld)=(answers,finalWorld) := Except.ok.inj accepted
    cases equal
    obtain ⟨entry,prepared,run⟩ := call_history fetch lookupDecoder removeDecoder replaceDecoder
      trace cmp constCmp byte bh permissions onlineCPUs externalActions environment access
      facts ready admissible.1 first
    refine ⟨entry,prepared,?_⟩
    apply eventually_weaken (historyStep fetch) _ _ _ _ run
    rintro final ⟨observed,ready,frame⟩
    have tail := ih ready (admissible.2 answer middle first) later
    apply Execute.mono tail
    rintro records last ⟨ready,matched,restFrame⟩
    exact ⟨ready,.cons observed matched,frame_trans frame restFrame⟩

/-- Arbitrary finite admissible sequences over one retained heap and one
allocation interpretation. Every binary call terminates with its ordered
interface observation; reconstruction and all resources compose from the
single executable initial check. Caller setup is explicit, not compiled. -/
theorem sequence_checked (fetch : Int64 → Option Decoded)
    (lookupDecoder : AnchoredDecoderAgreement fetch)
    (removeDecoder : IndexRemoveDecoderAgreement fetch)
    (replaceDecoder : IndexReplaceDecoderAgreement fetch)
    (trace : TracePcContract fetch) (cmp : TraceCmp4Contract fetch)
    (constCmp : TraceConstCmp4Contract fetch) (byte : TraceConstCmp1Contract fetch)
    (bh : BhEnableContract fetch) (permissions : Permissions) (onlineCPUs : Nat) (externalActions : List Nat)
    {n o c initial w ra calls answers finalWorld}
    (environment : SerializedEnvironment onlineCPUs externalActions)
    (access : ReturningDomainPermissions fetch permissions ra (EntryDomain n initial ra))
    (checked : initialCheck n o c initial w ra=.ok ())
    (admissible : AdmissibleSequence n calls w)
    (accepted : (program calls).run w=.ok (answers,finalWorld)) :
    Execute fetch n initial ra calls initial
      (SequencePost fetch permissions onlineCPUs externalActions n o c initial initial ra answers finalWorld) := by
  have facts := initial_facts checked
  exact sequence_from_ready fetch lookupDecoder removeDecoder replaceDecoder trace cmp constCmp byte bh
    permissions onlineCPUs externalActions environment access facts facts.ready admissible accepted

#print axioms sequence_checked
end Binary.Pair.Sequence
