import Std.Tactic.BVDecide
import Kraken.X64.OmniSemantics

theorem width8 (x y : BitVec 8) : (x ^^^ y) ^^^ y = x := by bv_decide
theorem width32 (x y : BitVec 32) : (x ^^^ y) ^^^ y = x := by bv_decide
theorem width64 (x y : BitVec 64) : (x ^^^ y) ^^^ y = x := by bv_decide
theorem compare8 (x : BitVec 8) : x = 32#8 ↔ x.toNat = 32 := by
  constructor
  · intro h; subst x; rfl
  · intro h; apply BitVec.eq_of_toNat_eq; exact h
theorem concrete8 : (32#8 == 32#8) = true := by decide
#print axioms width8
#print axioms width32
#print axioms width64
#print axioms compare8
#print axioms concrete8
#print axioms Operation.interp
#print axioms Executable.step
#print width8._native.bv_decide.ax_1_5
