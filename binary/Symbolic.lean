import Kraken.X64.OmniSemantics
import Kraken.X64.Parser

/- The first explicit CMP in wg_index_hashtable_lookup, at entry+0x59.
   R has already related EBP to the entry index and R12D to the query.
   The preceding coverage call is a separate instrumentation contract. -/
def firstCompare : Instr :=
  .regular .W64 .W32 (.cmp (.reg (.low .rbp .W32)) (.reg (.low .r12 .W32)))

theorem firstCompare_condition [Labels] (s : MachineData) (p : Std.Rco Int64) :
    (firstCompare.interp s p
      (fun d => .done ⟨d, p.upper⟩) (fun pc d => .done ⟨d, pc⟩)).All
      (fun t => t.data.status.zf =
        (s.regs.get (.low .rbp .W32) == s.regs.get (.low .r12 .W32))) := by
  simp only [firstCompare, Instr.interp, Operation.interp, RegOrMem.interp,
    Operand.interp, Effects.All, StatusFlags.from_result]
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.sub_eq_iff_eq_add]

#print axioms firstCompare_condition

def compareAndBranch : List (Kraken.Sized Directive) :=
  [⟨.instr firstCompare, 3⟩,
   ⟨.instr (.regular .W64 .W64 (.jcc .z "matched")), 2⟩]

/-- A whole comparison/branch region, with arbitrary registers and memory.
    UInt32 equality is exactly the mirror's Nat equality under R's bounds. -/
theorem compareAndBranch_correct [Labels] (s : MachineData) (pc : Int64) :
    (Directives.interp compareAndBranch s pc (fun p d => .done ⟨d, p⟩)).All
      (fun t => t.pc = if (s.regs.get (.low .rbp .W32)).toNat ==
                          (s.regs.get (.low .r12 .W32)).toNat
                      then label "matched" else pc + 5) := by
  have h (a b : BitVec 32) : (a - b == 0#32) = (a.toNat == b.toNat) := by
    apply Bool.eq_iff_iff.mpr
    simp [BitVec.sub_eq_iff_eq_add, BitVec.toNat_inj]
  simp [compareAndBranch, Directives.interp, Directive.interp, firstCompare,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    Effects.All, StatusFlags.from_result, CondCode.interp, h]
  split <;> simp_all [Effects.All, Int64.add_assoc]

#print axioms compareAndBranch_correct
