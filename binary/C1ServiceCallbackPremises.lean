import C1Interfaces
import C1ServiceCallbacks
import C1ServiceCallbackContracts
import C1ServiceJointFetch
import C1ServiceStubContract
import C1ServiceStubIdle

/-! Result C1, work package 4: `Premises` at the common decoder, and
`PremisesMet`.

`premises_of_contract`: for any stub code inside the stub's interval and any
layout and allocator whose contract that code meets, every other premise
holds of `Joint.fetch`, the callbacks being the image's.

`premisesMet` closes the interface proposition with the stub of
`C1ServiceStub` (twelve instructions at `allocEntry`, one at `freeEntry`),
which meets `AllocatorContract` as signed (`Stub.contract`), and whose `Idle`
holds of actual memories (`Stub.idle_initial`). The proposition itself does
not ask that `Idle` can hold: an allocator that is never idle would also
close it. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.TrustBase Binary.Statements.C1

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

/-- The stub's code lies in the stub's interval. -/
theorem stub_within : Joint.Within Stub.fetch Joint.stubLow Joint.stubHigh := by
  intro pc decoded here
  unfold Stub.fetch at here
  cases first : Image.fetchIn allocEntry Stub.allocCode pc with
  | some found =>
    have range := Callback.Text.fetchIn_address first (by decide +kernel)
    have low : Joint.stubLow ≤ allocEntry.toBitVec.toNat := by decide +kernel
    have high : allocEntry.toBitVec.toNat + Callback.Text.extent Stub.allocCode ≤ Joint.stubHigh := by
      decide +kernel
    omega
  | none =>
    rw [first] at here
    have range := Callback.Text.fetchIn_address (show Image.fetchIn freeEntry Stub.freeCode pc =
      some decoded from here) (by decide +kernel)
    have low : Joint.stubLow ≤ freeEntry.toBitVec.toNat := by decide +kernel
    have high : freeEntry.toBitVec.toNat + Callback.Text.extent Stub.freeCode ≤ Joint.stubHigh := by
      decide +kernel
    omega

/-- Every premise at the common decoder with the stub, for any table and peers. -/
theorem premises_with_stub (tableAt : Nat) (peers : List (PeerId × Nat)) :
    Premises (Joint.fetch Stub.fetch) (Stub.layout tableAt peers) Stub.allocator ∧
      CallbacksFromImage (Joint.fetch Stub.fetch) :=
  premises_of_contract stub_within (Stub.contract (Joint.stub_agrees stub_within) tableAt peers)

/-- ACCEPTANCE. -/
theorem premisesMet : PremisesMet :=
  ⟨_,_,_,(premises_with_stub 0 []).1,(premises_with_stub 0 []).2,by decide,
    _,[],Stub.idle_initial {} [] (by decide) (by simp) (by simp)⟩

#print axioms premises_of_contract
#print axioms premises_with_stub
#print axioms premisesMet
end Binary.Statements.C1.Proof
