import LookupReturnSimulation
import LookupStackFrame

namespace Binary.LookupRelation
open Leanux TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

/-- The still-live outer saved words, separate from the disposable helper
    scratch and the callback return slot. This is a proved frame invariant,
    not an additional entry premise or relation clause. -/
structure OuterSaved (entry current : MachineData) : Prop where
  stack : current.regs.rsp = entry.regs.rsp-40
  saved : current.regs.r15 = entry.regs.r15
  memory : ∀ a, InRange (entry.regs.rsp.toBitVec-40) 48 a →
    (Lookup.saveMemory entry 6).get? a = current.dmem.get? a

theorem OuterSaved.frame {entry before after : MachineData} (saved : OuterSaved entry before)
    (stack : after.regs.rsp = before.regs.rsp) (r15 : after.regs.r15 = before.regs.r15)
    (writes : Address → Prop) (frame : EqualOutside writes before.dmem after.dmem)
    (apart : ∀ a, InRange (entry.regs.rsp.toBitVec-40) 48 a → ¬writes a) :
    OuterSaved entry after :=
  ⟨stack.trans saved.stack, r15.trans saved.saved,
    fun a inside => (saved.memory a inside).trans (frame a (apart a inside))⟩

def outerWords (entry : MachineData) (returnAddress : UInt64) : List UInt64 :=
  [entry.regs.rbx, entry.regs.rbp, entry.regs.r12, entry.regs.r13, entry.regs.r14, returnAddress]

/-- Recover all six epilogue loads from the original prologue's saved
    memory and the actual entry return word. -/
theorem OuterSaved.loads (entry current : MachineData) (returnAddress : UInt64)
    (saved : OuterSaved entry current)
    (returnWord : entry.dmem.loadInt entry.regs.rsp.toBitVec 8 = some (returnAddress.toNat : Int)) :
    ∀ i < 6, current.dmem.loadInt (current.regs.rsp.toBitVec + .ofNat 64 (8*i)) 8 =
      some (((outerWords entry returnAddress)[i]?.getD 0).toNat : Int) := by
  intro i hi
  have byteFrame : EqualOutside (fun a => ¬InRange (entry.regs.rsp.toBitVec-40) 48 a)
      (Lookup.saveMemory entry 6) current.dmem := by
    classical
    intro a outside
    exact saved.memory a (Classical.not_not.mp outside)
  have location : current.regs.rsp.toBitVec = entry.regs.rsp.toBitVec-40 := by rw [saved.stack]; rfl
  have read := byteFrame.loadInt (current.regs.rsp.toBitVec + .ofNat 64 (8*i)) 8 (by
    intro j hj outside
    apply outside
    refine ⟨8*i+j, by omega, ?_⟩
    simp only [location, BitVec.ofNat_add, BitVec.add_assoc])
  rw [← read, location]
  have earlier (n : Nat) (hn : n < 5) :
      entry.regs.rsp.toBitVec-40+.ofNat 64 (8*n) = Lookup.slot entry (4-n) := by
    have number : 40 = (4-n+1)*8+8*n := by omega
    rw [show (40 : BitVec 64) = .ofNat 64 40 from rfl, number, BitVec.ofNat_add,
      ← BitVec.sub_sub, BitVec.sub_add_cancel]
    rfl
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
  | (rw [earlier _ (by decide), Lookup.saveMemory_read entry 6 _ (by decide) (by decide)]; rfl)
  | (change (Lookup.saveMemory entry 6).loadInt (entry.regs.rsp.toBitVec-40+40) 8 = some (returnAddress.toNat : Int)
     rw [BitVec.sub_add_cancel, Lookup.saveMemory_return entry 6 (by decide)]
     exact returnWord)

/-- Close the physical ABI return against the original entry frame, not
    merely against a marker or an arbitrary supplied saved-register tuple. -/
theorem return_from_saved (fetch : Int64 → Option Decoded) (agree : AnchoredDecoderAgreement fetch)
    (c : Config) (world : World) (entry current : MachineData) (returnAddress : UInt64)
    (saved : OuterSaved entry current)
    (returnWord : entry.dmem.loadInt entry.regs.rsp.toBitVec 8 = some (returnAddress.toNat : Int))
    (history : List MachineState) (seen : List Point) (source : List MirrorHistory.Point)
    (related : R c history seen ⟨current, Image.Lookup.entry+0x89⟩ world)
    (observed : observe c.rxSection history = .ok seen)
    (matched : MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection history) seen source)
    (aligned : ExecutedCorrespondence.CutsAligned (R c) c.rxSection history source)
    (latest : source.getLast?.map (·.world) = some world)
    (inactive : helperActive seen = false) (noReturn : lastHelperReturn seen = none) :
    historySteps fetch 7 (fun final =>
      Returned ⟨entry, Image.Lookup.entry⟩ final.machine returnAddress ∧
      final.machine.data.regs.rax = current.regs.rbx ∧
      final.machine.data.dmem = current.dmem ∧
      observe c.rxSection final.history = .ok (seen ++ [returned "wg_index_hashtable_lookup" final.machine]) ∧
      MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history)
        (seen ++ [returned "wg_index_hashtable_lookup" final.machine]) (source ++ [⟨.returned "wg_index_hashtable_lookup", world⟩]) ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history (source ++ [⟨.returned "wg_index_hashtable_lookup", world⟩]) ∧
      R c final.history (seen ++ [returned "wg_index_hashtable_lookup" final.machine]) final.machine world ∧
      ∃ suffix, final.history = history ++ suffix ∧
        ∀ q ∈ suffix, q.data.dmem = current.dmem)
      ⟨⟨current, Image.Lookup.entry+0x89⟩, history⟩ := by
  have loads := saved.loads entry current returnAddress returnWord
  have run := return_simulation fetch agree c world current history seen source related observed matched aligned latest
    inactive noReturn entry.regs.rbx entry.regs.rbp entry.regs.r12 entry.regs.r13 entry.regs.r14 returnAddress
    (by simpa [outerWords] using loads 0 (by decide))
    (by simpa [outerWords] using loads 1 (by decide))
    (by simpa [outerWords] using loads 2 (by decide))
    (by simpa [outerWords] using loads 3 (by decide))
    (by simpa [outerWords] using loads 4 (by decide))
    (by simpa [outerWords] using loads 5 (by decide))
  apply historySteps_mono fetch 7 _ _ _ _ run
  rintro final ⟨machine, recorded, full, matching, cuts, endpoint⟩
  refine ⟨?_, by rw [machine]; rfl, by rw [machine]; rfl, full, matching, cuts, endpoint,
    _, recorded, ?_⟩
  · rw [machine]
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, saved.saved⟩
    change current.regs.rsp+48 = entry.regs.rsp+8
    rw [saved.stack]
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_sub]
    change entry.regs.rsp.toBitVec-40+48 = entry.regs.rsp.toBitVec+8
    rw [show (48 : BitVec 64) = 40+8 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]

  · intro q member
    simp only [LookupReturn.restoreStates, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

#print axioms OuterSaved.frame
#print axioms OuterSaved.loads
#print axioms return_from_saved
end Binary.LookupRelation
