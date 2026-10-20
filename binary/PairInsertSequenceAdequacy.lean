import PairInsertSequenceExecution

namespace Binary.Pair.InsertSequence
open Leanux Leanux.WG TrustBase
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 2048

/-- Source-only obligations along accepted prefixes, with no future binary
preconditions, successful executions or reconstruction assumptions. -/
def AdmissibleSequence (n : Names) : List Call → World → Prop
  | [],_ => True
  | call::rest,w => Admissible n call w ∧ ∀ answer next,
      (source call).run w=.ok (answer,next) → AdmissibleSequence n rest next

/-- Exact intermediate source worlds, obtained from actual mirror calls.
They let the public postcondition expose reconstruction at every return. -/
inductive SourceBoundaries : List Call → World → List (Answer×World) → World → Prop where
  | nil (w) : SourceBoundaries [] w [] w
  | cons {call calls w answer next boundaries final}
      (first : (source call).run w=.ok (answer,next))
      (rest : SourceBoundaries calls next boundaries final) :
      SourceBoundaries (call::calls) w ((answer,next)::boundaries) final

def Boundary (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (onlineCPUs : Nat) (externalActions : List Nat) (n : Names) (o : Offsets)
    (c : CommonBitsCoverage.Context) (base : MachineState) (ra : UInt64)
    (config : RandomProvider.Config) (inputAt : DataMem → List HiddenRecord → Prop)
    (source : Answer×World) (record : CallRecord) : Prop :=
  Observed fetch permissions onlineCPUs externalActions n ra source.1 record ∧
    Ready n o c base record.2.machine source.2 config inputAt

def SequencePost (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (onlineCPUs : Nat) (externalActions : List Nat) (n : Names) (o : Offsets)
    (c : CommonBitsCoverage.Context) (base current : MachineState) (ra : UInt64)
    (config : RandomProvider.Config) (inputAt : DataMem → List HiddenRecord → Prop)
    (calls : List Call) (w : World) (answers : List Answer) (finalWorld : World)
    (records : List CallRecord) (final : MachineState) : Prop :=
  Ready n o c base final finalWorld config inputAt ∧
    (∃ boundaries, SourceBoundaries calls w boundaries finalWorld ∧ boundaries.map Prod.fst=answers ∧
      Mapped (Boundary fetch permissions onlineCPUs externalActions n o c base ra config inputAt) boundaries records) ∧
    EqualOutside (Writes n o c base config) current.data.dmem final.data.dmem

theorem sequence_from_ready (fetch : Int64 → Option Decoded)
    (lookupDecoder : AnchoredDecoderAgreement fetch)
    (removeDecoder : IndexRemoveDecoderAgreement fetch)
    (replaceDecoder : IndexReplaceDecoderAgreement fetch)
    (insertDecoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) (cmp : TraceCmp4Contract fetch)
    (constCmp : TraceConstCmp4Contract fetch) (byte : TraceConstCmp1Contract fetch)
    (bh : BhEnableContract fetch) (permissions : Permissions) (onlineCPUs : Nat) (externalActions : List Nat)
    {n o c base initialWorld ra current w calls answers finalWorld config inputAt}
    (environment : SerializedEnvironment onlineCPUs externalActions)
    (access : ReturningDomainPermissions fetch permissions ra (EntryDomain n o c base ra config inputAt))
    (physical : RandomReturnContract fetch config)
    (coupling : RandomInputCoupling fetch config c.coverage (c.preempt+512)
      (Insert.codeEntry+0x79).toUInt64 inputAt)
    (facts : InitialFacts n o c base initialWorld ra config)
    (ready : Ready n o c base current w config inputAt)
    (admissible : AdmissibleSequence n calls w)
    (accepted : (program calls).run w=.ok (answers,finalWorld)) :
    Execute fetch n base ra calls current
      (SequencePost fetch permissions onlineCPUs externalActions n o c base current ra config inputAt calls w answers finalWorld) := by
  induction calls generalizing current w answers finalWorld with
  | nil =>
    change Except.ok ([],w)=Except.ok (answers,finalWorld) at accepted
    cases Except.ok.inj accepted
    exact ⟨ready,⟨[],.nil w,rfl,.nil⟩,fun _ _ => rfl⟩
  | cons call rest ih =>
    change ((source call).run w >>= fun p => (program rest).run p.2 >>= fun q =>
      .ok (p.1::q.1,q.2))=.ok (answers,finalWorld) at accepted
    obtain ⟨⟨answer,middle⟩,first,accepted⟩ := bind_ok accepted
    obtain ⟨⟨remaining,lastWorld⟩,later,accepted⟩ := bind_ok accepted
    cases Except.ok.inj accepted
    obtain ⟨entry,prepared,run⟩ := call_history fetch lookupDecoder removeDecoder replaceDecoder insertDecoder
      trace cmp constCmp byte bh permissions onlineCPUs externalActions environment access physical coupling
      facts ready admissible.1 first
    refine ⟨entry,prepared,?_⟩
    apply eventually_weaken (historyStep fetch) _ _ _ _ run
    rintro final ⟨observed,next,frame⟩
    have tail := ih next (admissible.2 answer middle first) later
    apply Execute.mono tail
    rintro records last ⟨lastReady,⟨boundaries,sourceTrace,answersEqual,matched⟩,restFrame⟩
    refine ⟨lastReady,⟨(answer,middle)::boundaries,.cons first sourceTrace,?_,
      .cons ⟨observed,next⟩ matched⟩,frame_trans frame restFrame⟩
    exact congrArg (answer :: ·) answersEqual

/-- Arbitrary finite accepted mixed sequences, from one checked physical
entry state and one supplied input interpretation. The actual four anchors
share a retained heap and allocation interpretation. Every next Pre is
derived; no rematerialization or future successful binary call is assumed.
The sequential environment and unproved services remain explicit hypotheses. -/
theorem sequence_checked (fetch : Int64 → Option Decoded)
    (lookupDecoder : AnchoredDecoderAgreement fetch)
    (removeDecoder : IndexRemoveDecoderAgreement fetch)
    (replaceDecoder : IndexReplaceDecoderAgreement fetch)
    (insertDecoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) (cmp : TraceCmp4Contract fetch)
    (constCmp : TraceConstCmp4Contract fetch) (byte : TraceConstCmp1Contract fetch)
    (bh : BhEnableContract fetch) (permissions : Permissions) (onlineCPUs : Nat) (externalActions : List Nat)
    {n o c initial w ra calls answers finalWorld config inputAt records}
    (environment : SerializedEnvironment onlineCPUs externalActions)
    (access : ReturningDomainPermissions fetch permissions ra (EntryDomain n o c initial ra config inputAt))
    (physical : RandomReturnContract fetch config)
    (coupling : RandomInputCoupling fetch config c.coverage (c.preempt+512)
      (Insert.codeEntry+0x79).toUInt64 inputAt)
    (checked : initialCheck n o c initial w ra config=.ok ())
    (supplied : w.hidden=some records) (input : inputAt initial.data.dmem records)
    (admissible : AdmissibleSequence n calls w)
    (accepted : (program calls).run w=.ok (answers,finalWorld)) :
    Execute fetch n initial ra calls initial
      (SequencePost fetch permissions onlineCPUs externalActions n o c initial initial ra config inputAt calls w answers finalWorld) := by
  have facts := initial_facts checked
  exact sequence_from_ready fetch lookupDecoder removeDecoder replaceDecoder insertDecoder trace cmp constCmp byte bh
    permissions onlineCPUs externalActions environment access physical coupling facts
    (facts.ready supplied input) admissible accepted

#print axioms sequence_checked
end Binary.Pair.InsertSequence
