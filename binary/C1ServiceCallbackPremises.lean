import C1Interfaces
import C1ServiceCallbacks
import C1ServiceCallbackContracts
import C1ServiceJointFetch

/-! Result C1, work package 4: `Premises` at the common decoder, and
`PremisesMet`.

`premises_of_contract` is the part with content: for any stub code inside the
stub's interval and any layout and allocator whose contract that code meets,
every other premise holds of `Joint.fetch`, the callbacks being the image's.

`premisesMet` closes the interface proposition AS STATED, with an allocator
whose `Idle` never holds. The proposition does not ask for more: it has no
clause that makes the allocator's contract bite (only `Witness` does, by
demanding `Idle` of an actual state). -/
namespace Binary.Statements.C1.Proof
open Binary.TrustBase Binary.Statements.C1

/-- Every premise but the allocator's contract, and the callbacks from the
image, at the common decoder. -/
theorem premises_of_contract {stub : Int64 → Option Decoded}
    (within : Joint.Within stub Joint.stubLow Joint.stubHigh) {L : Layout} {A : Allocator}
    (contract : AllocatorContract (Joint.fetch stub) L A) :
    Premises (Joint.fetch stub) L A ∧ CallbacksFromImage (Joint.fetch stub) := by
  have services : ServiceDecoderAgreement (Joint.fetch stub) := Joint.services_agree
  have image : CallbacksFromImage (Joint.fetch stub) := ⟨services,Joint.entries_agree⟩
  exact ⟨{
    insertion := Joint.mutation_agrees within
    lookup := Joint.allowedips_agrees within
    peer := Joint.anchored_agrees within
    tracePc := Callback.pc_contract _ services
    callbacks := ⟨Callback.Text.pc_contract _ services,Callback.Text.const_cmp1_contract _ services,
      cmp8FromImage _ image⟩
    cmp1 := cmp1FromImage _ image
    constCmp4 := Callback.Text.const_cmp4_contract _ services
    bhEnable := Callback.Text.bh_contract _ services
    allocator := contract },image⟩

/-- An allocator that is never idle: every clause of the contract holds of it
vacuously, whatever code is at the two service addresses. -/
def neverIdle : Allocator := ⟨fun _ _ _ => False,8⟩

theorem neverIdle_contract (fetch : Int64 → Option Decoded) (L : Layout) :
    AllocatorContract fetch L neverIdle :=
  ⟨fun _ _ _ _ idle _ => idle,
   fun _ _ _ _ _ _ _ _ _ _ _ _ idle => False.elim idle,
   fun _ _ _ _ _ _ _ _ _ _ _ idle => False.elim idle⟩

theorem no_stub : Joint.Within (fun _ => none) Joint.stubLow Joint.stubHigh :=
  fun _ _ here => by cases here

/-- ACCEPTANCE (as stated; see the module comment for what it does not show). -/
theorem premisesMet : PremisesMet :=
  have met := premises_of_contract no_stub (neverIdle_contract (Joint.fetch fun _ => none) ⟨0,[],[],0⟩)
  ⟨_,_,_,met.1,met.2,by decide⟩

#print axioms premises_of_contract
#print axioms premisesMet
end Binary.Statements.C1.Proof
