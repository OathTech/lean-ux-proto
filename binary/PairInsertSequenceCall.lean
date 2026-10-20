import SourceAdapter
import PairInsertSequencePre
import PairSequenceInputFrame
import PairSequenceCall

namespace Binary.Pair.InsertSequence
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 2048

theorem prepare_system {n base ra call current entry}
    (prepared : Sequence.prepare n base ra call current=.ok entry) :
    entry.data.system=current.data.system := by
  cases call with
  | lookup query kinds => cases prepared; rfl
  | remove owner =>
    change (addressOf n owner >>= fun address => .ok
      (Sequence.install n base ra (.ofNat Remove.entry) address 0 current))=.ok entry at prepared
    obtain ⟨address,_,equal⟩ := bind_ok prepared
    cases Except.ok.inj equal
    rfl
  | replace pid kid =>
    change (addressOf n (.handshake pid) >>= fun old => addressOf n (.keypair kid) >>= fun new =>
      .ok (Sequence.install n base ra (.ofNat Replace.entry) old new current))=.ok entry at prepared
    obtain ⟨old,_,rest⟩ := bind_ok prepared
    obtain ⟨new,_,equal⟩ := bind_ok rest
    cases Except.ok.inj equal
    rfl

theorem frame_trans {n o c base config first second third}
    (a : EqualOutside (Writes n o c base config) first second)
    (b : EqualOutside (Writes n o c base config) second third) :
    EqualOutside (Writes n o c base config) first third :=
  fun address outside => (a address outside).trans (b address outside)

theorem insert_writes {n o c base config ra pc arg2 arg3 current a}
    (written : Insert.Writes n o config c (Sequence.install n base ra pc arg2 arg3 current) a) :
    Writes n o c base config a := by
  rcases written with heap | privateByte | stack | buffer | preempt
  · exact .inl heap
  · exact .inr (.inr (.inr (.inr (.inl privateByte))))
  · exact .inr (.inl (stack_live stack))
  · exact .inr (.inr (.inl buffer))
  · exact .inr (.inr (.inr (.inl preempt)))

def Interface (n : Names) (ra : UInt64) (entry final : MachineState) : Answer → Prop
  | .existing answer => Sequence.Interface n ra entry final answer
  | .insert answer => Returned entry final ra ∧ final.data.regs.rax.toNat=answer

theorem Interface.returned {n ra entry final answer} (h : Interface n ra entry final answer) :
    Returned entry final ra := by cases answer <;> exact h.1

def Post (n : Names) (o : Offsets) (c : Context) (base : MachineState) (ra : UInt64)
    (config : RandomProvider.Config) (inputAt : DataMem → List HiddenRecord → Prop)
    (current entry : MachineState) (answer : Answer) (w : World) (final : MachineState) : Prop :=
  Interface n ra entry final answer ∧ Ready n o c base final w config inputAt ∧
    EqualOutside (Writes n o c base config) current.data.dmem final.data.dmem

/-- Every next Pre and preserved input interpretation follows from the same
retained resources, using the individual function theorems unchanged. -/
theorem call_checked (fetch : Int64 → Option Decoded)
    (lookupDecoder : AnchoredDecoderAgreement fetch)
    (removeDecoder : IndexRemoveDecoderAgreement fetch)
    (replaceDecoder : IndexReplaceDecoderAgreement fetch)
    (insertDecoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) (cmp : TraceCmp4Contract fetch)
    (constCmp : TraceConstCmp4Contract fetch) (byte : TraceConstCmp1Contract fetch)
    (bh : BhEnableContract fetch)
    {n o c base initialWorld ra current w call answer finalWorld config inputAt}
    (physical : RandomReturnContract fetch config)
    (coupling : RandomInputCoupling fetch config c.coverage (c.preempt+512)
      (Insert.codeEntry+0x79).toUInt64 inputAt)
    (facts : InitialFacts n o c base initialWorld ra config)
    (ready : Ready n o c base current w config inputAt)
    (admissible : Admissible n call w)
    (accepted : (source call).run w=.ok (answer,finalWorld)) :
    ∃ entry, prepare n base ra call current=.ok entry ∧
      Eventually (instructionStep fetch)
        (Post n o c base ra config inputAt current entry answer finalWorld) entry := by
  cases call with
  | existing call =>
    change ((Sequence.source call).run w >>= fun p => .ok (.existing p.1,p.2))=.ok (answer,finalWorld) at accepted
    obtain ⟨⟨value,world⟩,first,equal⟩ := bind_ok accepted
    cases Except.ok.inj equal
    obtain ⟨entry,prepared,executed⟩ := Sequence.call_checked fetch lookupDecoder removeDecoder replaceDecoder
      trace cmp constCmp byte bh facts.previous ready.previous admissible first
    refine ⟨entry,prepared,?_⟩
    have mode := prepare_system prepared
    apply eventually_weaken (instructionStep fetch) _ _ _ _ (SystemInvariant.eventually_mode fetch executed)
    rintro final ⟨⟨interface,next,frame⟩,privilege,direction⟩
    have wideFrame : EqualOutside (Writes n o c base config) current.data.dmem final.data.dmem :=
      fun a outside => frame a (fun written => outside (existing_writes written))
    have privateFrame := facts.private_frame frame
    refine ⟨interface,⟨next,⟨?_,?_,?_,next.mapped⟩,?_,?_⟩,wideFrame⟩
    · rw [←RandomProvider.check_frame privateFrame]
      exact ready.provider.privateCheck
    · rw [privilege,mode]
      exact ready.provider.privilege
    · rw [direction,mode]
      exact ready.provider.direction
    · intro needed
      exact (facts.pending_frame wideFrame needed).symm.trans (ready.nestedPending needed)
    · obtain ⟨records,supplied,input⟩ := ready.input
      obtain ⟨d,device,_,_⟩ := ready.previous.state
      exact ⟨records,(Sequence.input_frame device first).trans supplied,
        coupling.frame _ _ records privateFrame input⟩
  | insert owner =>
    obtain ⟨address,named⟩ := admissible
    change ((Source.indexInsert owner).run w >>= fun p => .ok (.insert p.1,p.2))=.ok (answer,finalWorld) at accepted
    obtain ⟨⟨value,world⟩,first,equal⟩ := bind_ok accepted
    cases Except.ok.inj equal
    let entry := Sequence.install n base ra Insert.codeEntry address 0 current
    have next := install_ready facts ready coupling Insert.codeEntry address 0
    obtain ⟨records,supplied,input⟩ := next.input
    refine ⟨entry,?_,?_⟩
    · simp only [prepare,named]
      rfl
    · have executed := Insert.insert_checked fetch insertDecoder trace cmp bh physical coupling
        (insert_pre facts ready coupling named) supplied input first
      apply eventually_weaken (instructionStep fetch) _ _ _ _ executed
      rintro final ⟨returned,result,memory,state,provider,tape,frame,kinds⟩
      have whole : EqualOutside (Writes n o c base config) current.data.dmem final.data.dmem := by
        apply frame_trans (fun a outside => Sequence.install_writes n o c base ra Insert.codeEntry address 0 current a
          (fun written => outside (existing_writes written)))
        exact fun a outside => frame a (fun written => outside (insert_writes written))
      have mapped : ∀ a size, (base.data.dmem.loadInt a size).isSome=true →
          (final.data.dmem.loadInt a size).isSome=true :=
        fun a size prior => provider.mapped a size (next.provider.mapped a size prior)
      exact ⟨⟨returned,result⟩,⟨⟨state,memory.covered,memory.preempt,memory.pending false,mapped,
        next.previous.kinds.trans kinds⟩,⟨provider.privateCheck,provider.privilege,provider.direction,mapped⟩,
        (fun needed => (facts.pending_frame whole needed).symm.trans (ready.nestedPending needed)),tape⟩,whole⟩

#print axioms call_checked
end Binary.Pair.InsertSequence
