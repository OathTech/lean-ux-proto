import CallbackBh
import KcovInvariant
import CanonicalLoads

namespace Binary.Callback
open TrustBase
local instance : Labels := Image.linkedLabels

def WritesReady (memory : Mem 64) (rsp : UInt64) (writes : List WordWrite) : Prop :=
  ∀ w ∈ writes, (memory.loadInt w.address 8).isSome=true ∧
    ∀ a, InRange w.address 8 a → ¬InRange rsp.toBitVec 8 a

def StoresPost (s : MachineData) (ra : UInt64) (writes : List WordWrite)
    (t : MachineState) : Prop :=
  Returned ⟨s,0⟩ t ra ∧ t.data.dmem=Kcov.storesMemory writes s.dmem

theorem stores_return (s : MachineData) (ra : UInt64) (writes : List WordWrite)
    (ready : WritesReady s.dmem s.regs.rsp writes)
    (read : s.dmem.loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int)) :
    (Kcov.storesMemory writes s.dmem).loadInt s.regs.rsp.toBitVec 8=some (ra.toNat : Int) := by
  have frame := Kcov.stores_frame writes s.dmem
    (fun a => ¬InRange s.regs.rsp.toBitVec 8 a) (by
      intro w member a inside
      exact (ready w member).2 a inside)
  exact (frame.loadInt s.regs.rsp.toBitVec 8 (by
    intro i hi outside
    exact outside ⟨i,hi,rfl⟩)).symm.trans read

theorem stores_post_contract {kind : KcovKind} {s : MachineState} {ra writes t}
    (plan : KcovPlan kind s=some writes)
    (post : StoresPost s.data ra writes t) :
    Returned s t ra ∧ EqualOutside (KcovWrites kind s) s.data.dmem t.data.dmem ∧
      KcovEffect kind s t := by
  refine ⟨post.1,?_,writes,plan,post.2⟩
  rw [post.2]
  exact Kcov.stores_frame writes s.data.dmem _ (by
    intro w member a inside
    exact ⟨writes,plan,w,member,inside⟩)

theorem callback_load64_raw (m : Mem 64) (base : BitVec 64) (word : BitVec 64)
    (read : load64 m base=some word) : m.loadInt base 8=some (word.toNat : Int) := by
  cases raw : m.loadInt base 8 with
  | none => simp [load64,raw] at read
  | some n =>
    have equal : word=BitVec.ofInt 64 n := by simpa [load64,raw] using read.symm
    obtain ⟨nonnegative,bound⟩ := loadInt_range m base 8 n raw
    rw [equal]
    congr 1
    simp only [BitVec.toNat_ofInt]
    rw [Int.emod_eq_of_lt nonnegative (by simpa using bound), Int.toNat_of_nonneg nonnegative]

theorem no_borrow_iff (x y : BitVec w) :
    (x-y).unsigned=x.unsigned-y.unsigned ↔ y.toNat≤x.toNat := by
  unfold BitVec.unsigned
  by_cases le : y.toNat≤x.toNat
  · rw [BitVec.toNat_sub_of_le (show y≤x from le)]
    omega
  · have nonnegative := (x-y).toNat
    omega

theorem ah_mask (x : BitVec 64) :
    ((x.extractLsb' 8 56).extractLsb' 0 8 &&& 1#8=0#8) ↔
      (x.extractLsb' 0 32 &&& 256#32=0#32) := by
  change (_ &&& BitVec.twoPow 8 0=0#8) ↔ (_ &&& BitVec.twoPow 32 8=0#32)
  rw [BitVec.and_twoPow,BitVec.and_twoPow]
  simp only [BitVec.getLsbD_extractLsb']
  cases x.getLsbD 8 <;> simp
  decide +kernel

end Binary.Callback
