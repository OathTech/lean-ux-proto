import PeerCountState
import PeerIncrementHistory
import ScanFrame

namespace Binary.PeerCountPhase
open PeerGet
local instance : Labels := Image.linkedLabels

theorem At.functional {pending memory address first second}
    (hf : At pending memory address first) (hs : At pending memory address second) : first = second := by
  cases pending with
  | none =>
    have equal := Option.some.inj (hf.symm.trans hs)
    omega
  | some p =>
    by_cases selected : address = p.address
    · simp only [At, selected, ite_true] at hf hs
      exact hf.1.trans hs.1.symm
    · simp only [At, selected, ite_false] at hf hs
      have equal := Option.some.inj (hf.symm.trans hs)
      omega

theorem At.frame {pending before after address count writes}
    (same : EqualOutside writes before after)
    (apart : ∀ i < 4, ¬writes (address + .ofNat 64 i))
    (represented : At pending before address count) : At pending after address count := by
  have equal := same.loadInt address 4 apart
  cases pending with
  | none => exact equal.symm.trans represented
  | some p =>
    by_cases selected : address = p.address
    · subst address
      simp only [At, ite_true] at represented ⊢
      exact ⟨represented.1, equal.symm.trans represented.2⟩
    · simp only [At, selected, ite_false] at represented ⊢
      exact equal.symm.trans represented

theorem scan_splice (pending : Option Pending) (front : List MachineState)
    (shared : MachineState) (back : List MachineState) :
    scan pending (front ++ shared :: back) = scan (scan pending (front ++ [shared])) (shared :: back) := by
  induction front generalizing pending with
  | nil => rfl
  | cons before front ih =>
    cases front with
    | nil => rfl
    | cons after front =>
      simpa only [List.cons_append, scan] using ih (edge pending before after)

theorem scan_snoc (pending : Option Pending) (history : List MachineState)
    (before after : MachineState) (last : history.getLast? = some before) :
    scan pending (history ++ [after]) = edge (scan pending history) before after := by
  have restored := LookupHistory.history_restore last
  rw [← restored]
  rw [List.append_assoc, List.singleton_append]
  exact scan_splice pending history.dropLast before [after]

/-- Establish the phase from the actual successful CMPXCHG successor used
    by inc_cmpxchg_history. No old count is supplied independently. -/
theorem increment_edge (pending : Option Pending) (s : MachineData) :
    edge pending ⟨incMove s, Image.PeerGet.entry+0x4a⟩
      ⟨incCompare s, Image.PeerGet.entry+0x4f⟩ =
      some ⟨s.regs.r13.toBitVec, s.regs.get (.low .rbp .W32)⟩ := by
  simp [edge, incMove, incLea, incCompare, MachineData.setReg,
    StatusFlags.from_result, Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Image.PeerGet.entry]
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp

/-- The old source count is represented immediately after the executed
    store, although current physical memory already contains old+1. -/
theorem increment_at (s : MachineData) :
    At (some ⟨s.regs.r13.toBitVec, s.regs.get (.low .rbp .W32)⟩)
      (incCompare s).dmem s.regs.r13.toBitVec (s.regs.get (.low .rbp .W32)).toNat := by
  simp only [At, ite_true, true_and]
  exact load32_store _ _ _

theorem return_edge (pending : Option Pending) (s : MachineData) (after : MachineState) :
    edge pending ⟨s, Image.PeerGet.entry+0xaf⟩ after = none := by
  simp only [edge, ite_true]

/-- After committing the source update, direct representation follows
    from the same physical count word. Acceptance supplies non-overflow;
    it is a theorem premise here, not an entry-domain restriction. -/
theorem commit_at {memory : Mem 64} (p : Pending) (count : Nat)
    (represented : At (some p) memory p.address count)
    (bound : count + 1 < 2^32) : At none memory p.address (count + 1) := by
  simp only [At, ite_true] at represented ⊢
  obtain ⟨countEq, loaded⟩ := represented
  rw [BitVec.toNat_add, show (1 : BitVec 32).toNat = 1 from rfl,
    ← countEq, Nat.mod_eq_of_lt bound] at loaded
  exact loaded

theorem unselected_at {memory : Mem 64} (p : Pending) (address : Address) (count : Nat)
    (different : address ≠ p.address) :
    At (some p) memory address count ↔ At none memory address count := by
  simp only [At, different, ite_false]

/-- The executed CMPXCHG both extends the real history and establishes the
    old source count under the phase derived from that extension. -/
theorem increment_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (initial : Option Pending)
    (last : history.getLast? = some ⟨incMove s, Image.PeerGet.entry+0x4a⟩)
    (count : s.dmem.loadInt s.regs.r13.toBitVec 4 =
      some (s.regs.get (.low .rbp .W32)).toNat) :
    historySteps fetch 1 (fun t =>
      t.machine = ⟨incCompare s, Image.PeerGet.entry+0x4f⟩ ∧
      t.history = history ++ [t.machine] ∧
      scan initial t.history = some ⟨s.regs.r13.toBitVec, s.regs.get (.low .rbp .W32)⟩ ∧
      At (scan initial t.history) t.machine.data.dmem s.regs.r13.toBitVec
        (s.regs.get (.low .rbp .W32)).toNat)
      ⟨⟨incMove s, Image.PeerGet.entry+0x4a⟩, history⟩ := by
  apply historySteps_mono fetch 1 _ _ _ _ (inc_cmpxchg_history fetch agree s history count)
  rintro t ⟨machine, recorded⟩
  have phase : scan initial t.history =
      some ⟨s.regs.r13.toBitVec, s.regs.get (.low .rbp .W32)⟩ := by
    rw [recorded, scan_snoc initial history _ _ last, machine, increment_edge]
  refine ⟨machine, recorded, phase, ?_⟩
  rw [phase, machine]
  exact increment_at s

theorem edge_silent (pending : Option Pending) (before after : MachineState)
    (outside : Image.fetch before.pc = none) : edge pending before after = pending := by
  have noReturn : before.pc ≠ Image.PeerGet.entry+0xaf := by
    intro equal
    rw [equal] at outside
    cases outside
  have noIncrement : before.pc ≠ Image.PeerGet.entry+0x4a := by
    intro equal
    rw [equal] at outside
    cases outside
  simp only [edge, noReturn, ite_false, noIncrement, false_and]

/-- Named service contracts retain all their states. Their no-reentry
    condition proves that those edges cannot reset or fabricate this phase. -/
theorem scan_service (pending : Option Pending) (history : List MachineState)
    (outside : TrustBase.NoAnchoredReentry history) : scan pending history = pending := by
  induction history generalizing pending with
  | nil => rfl
  | cons before rest ih =>
    cases rest with
    | nil => rfl
    | cons after rest =>
      have first : Image.fetch before.pc = none := outside before (by simp)
      have tail : TrustBase.NoAnchoredReentry (after :: rest) := by
        intro s member
        exact outside s (by simp only [List.dropLast_cons_cons, List.mem_cons]; exact Or.inr member)
      simp only [scan, edge_silent pending before after first]
      exact ih pending tail

#print axioms At.functional
#print axioms At.frame
#print axioms scan_splice
#print axioms scan_snoc
#print axioms increment_edge
#print axioms increment_at
#print axioms return_edge
#print axioms commit_at
#print axioms unselected_at
#print axioms increment_history
#print axioms edge_silent
#print axioms scan_service
end Binary.PeerCountPhase
