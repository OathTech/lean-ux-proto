import PairSequenceCall

namespace Binary.Pair.Sequence
open Leanux Leanux.WG TrustBase
local instance : Labels := Image.linkedLabels

abbrev CallRecord := MachineState × Executed

/-- An explicit caller transition followed by actual Kraken instruction
execution to each call boundary. No compiled caller instruction is claimed. -/
def Execute (fetch : Int64 → Option Decoded) (n : Names) (base : MachineState) (ra : UInt64) :
    List Call → MachineState → (List CallRecord → MachineState → Prop) → Prop
  | [],current,post => post [] current
  | call::rest,current,post => ∃ entry, prepare n base ra call current=.ok entry ∧
      Eventually (historyStep fetch)
        (fun final => Execute fetch n base ra rest final.machine
          (fun records last => post ((entry,final)::records) last)) ⟨entry,[entry]⟩

theorem Execute.mono {fetch n base ra calls current P Q}
    (run : Execute fetch n base ra calls current P)
    (imp : ∀ records final, P records final → Q records final) :
    Execute fetch n base ra calls current Q := by
  induction calls generalizing current P Q with
  | nil => exact imp [] current run
  | cons call rest ih =>
    obtain ⟨entry,prepared,run⟩ := run
    refine ⟨entry,prepared,?_⟩
    apply eventually_weaken (historyStep fetch) _ _ _ _ run
    intro final rest
    exact ih rest (fun records last => imp ((entry,final)::records) last)

def EntryDomain (n : Names) (base : MachineState) (ra : UInt64) (entry : MachineState) : Prop :=
  ∃ call current, prepare n base ra call current=.ok entry

def Observed (fetch : Int64 → Option Decoded) (permissions : Permissions)
    (onlineCPUs : Nat) (externalActions : List Nat) (n : Names) (ra : UInt64)
    (answer : Answer) (record : CallRecord) : Prop :=
  Interface n ra record.1 record.2.machine answer ∧
    ActualHistory fetch record.1 record.2.history ∧ record.2.history.getLast?=some record.2.machine ∧
    RunEnvironment fetch permissions onlineCPUs externalActions record.2.history

theorem call_history (fetch : Int64 → Option Decoded)
    (lookupDecoder : AnchoredDecoderAgreement fetch)
    (removeDecoder : IndexRemoveDecoderAgreement fetch)
    (replaceDecoder : IndexReplaceDecoderAgreement fetch)
    (trace : TracePcContract fetch) (cmp : TraceCmp4Contract fetch)
    (constCmp : TraceConstCmp4Contract fetch) (byte : TraceConstCmp1Contract fetch)
    (bh : BhEnableContract fetch) (permissions : Permissions) (onlineCPUs : Nat) (externalActions : List Nat)
    {n o c base initialWorld ra current w call answer finalWorld}
    (environment : SerializedEnvironment onlineCPUs externalActions)
    (access : ReturningDomainPermissions fetch permissions ra (EntryDomain n base ra))
    (facts : InitialFacts n o c base initialWorld ra) (ready : Ready n o c base current.data.dmem w)
    (admissible : Admissible n call w) (accepted : (source call).run w=.ok (answer,finalWorld)) :
    ∃ entry, prepare n base ra call current=.ok entry ∧
      Eventually (historyStep fetch) (fun final =>
        Observed fetch permissions onlineCPUs externalActions n ra answer (entry,final) ∧
        Ready n o c base final.machine.data.dmem finalWorld ∧
        EqualOutside (Writes n o c base) current.data.dmem final.machine.data.dmem) ⟨entry,[entry]⟩ := by
  obtain ⟨entry,prepared,physical⟩ := call_checked fetch lookupDecoder removeDecoder replaceDecoder
    trace cmp constCmp byte bh facts ready admissible accepted
  refine ⟨entry,prepared,?_⟩
  have history := history_lift fetch _ entry physical [entry]
  have actual := eventually_actual fetch entry _ _ history .start (by simp)
  have last := history_last fetch _ _ (by simp) actual
  apply eventually_weaken (historyStep fetch) _ _ _ _ last
  rintro t ⟨⟨⟨interface,ready,frame⟩,actual⟩,last⟩
  exact ⟨⟨interface,actual,last,environment,
    access entry ⟨call,current,prepared⟩ t.history t.machine actual last interface.1⟩,ready,frame⟩

#print axioms call_history
end Binary.Pair.Sequence
