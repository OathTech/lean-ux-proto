import CanonicalLoads

namespace Binary.Callback
open TrustBase

/-- Finite modular-byte separation; unlike interval arithmetic this admits
buffers whose addresses wrap at the architectural width. -/
def apart (a : BitVec 64) (n : Nat) (b : BitVec 64) (m : Nat) : Bool :=
  (List.range n).all fun i => (List.range m).all fun j =>
    a + .ofNat 64 i != b + .ofNat 64 j

theorem apart_sound {a n b m} (checked : apart a n b m = true) :
    ∀ address, InRange a n address → ¬InRange b m address := by
  rintro address ⟨i,hi,ei⟩ ⟨j,hj,ej⟩
  have neq := List.all_eq_true.mp
    (List.all_eq_true.mp checked i (List.mem_range.mpr hi)) j (List.mem_range.mpr hj)
  simp only [bne_iff_ne] at neq
  exact neq (ei.symm.trans ej)

def readyCheck (kind : KcovKind) (s : MachineState) : Bool :=
  match KcovPlan kind s with
  | none => false
  | some stores => stores.all fun w =>
      (s.data.dmem.loadInt w.address 8).isSome && apart w.address 8 s.data.regs.rsp.toBitVec 8

theorem readyCheck_sound {kind s} (checked : readyCheck kind s = true) : KcovReady kind s := by
  unfold readyCheck at checked
  split at checked
  · contradiction
  · rename_i stores plan
    refine ⟨stores,plan,?_⟩
    intro w hw
    have both : (s.data.dmem.loadInt w.address 8).isSome = true ∧
        apart w.address 8 s.data.regs.rsp.toBitVec 8 = true := by
      simpa only [Bool.and_eq_true] using List.all_eq_true.mp checked w hw
    exact ⟨both.1,apart_sound both.2⟩

def bhReadyCheck (s : MachineState) : Bool :=
  match load32 s.data.dmem preemptCountAddress with
  | none => false
  | some count => count &&& 0x000f0000 == 0 &&
      ((count + 1 - s.data.regs.get (.low .rsi .W32)) &&& 0x00ffff00 != 0 ||
        s.data.dmem.loadInt softirqPendingAddress 2 == some 0) &&
      apart preemptCountAddress 4 s.data.regs.rsp.toBitVec 8

theorem bhReadyCheck_sound {s} (checked : bhReadyCheck s = true) : BhEnableReady s := by
  unfold bhReadyCheck at checked
  cases read : load32 s.data.dmem preemptCountAddress with
  | none => simp only [read] at checked; contradiction
  | some count =>
    simp only [read, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, Bool.or_eq_true] at checked
    refine ⟨count,load32_raw _ _ _ read,checked.1.1,?_,apart_sound checked.2⟩
    intro zero
    rcases checked.1.2 with nonzero | pending
    · exact False.elim (nonzero zero)
    · exact pending

#print axioms readyCheck_sound
#print axioms bhReadyCheck_sound

end Binary.Callback
