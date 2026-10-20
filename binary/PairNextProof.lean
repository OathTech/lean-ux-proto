import PairMemory
import Regions

namespace Binary.Pair

/-- Connect the executable read, including its non-wrapping check, to the
very load used by Kraken. No evaluation axiom or native decision is used. -/
theorem word_loadInt (m : DataMem) (path : String) (a bytes value : Nat)
    (read : word m path a bytes = .ok value) :
    m.loadInt (.ofNat 64 a) bytes = some (value : Int) := by
  by_cases bound : a + bytes ≤ 2^64
  · cases h : m.loadBytes (.ofNat 64 a) bytes with
    | none => simp [word, bound, h] at read
    | some bs =>
      simp [word, bound, h] at read
      simp only [Mem.loadInt, h, Option.map_some]
      rw [← read, Int.toNat_of_nonneg (Int.ofBytes_ge_zero bs)]
  · simp [word, bound] at read

/-- Early symbolic feasibility check: the actual three-instruction loop back
edge preserves the very reconstruction executed by the paired runner, and
updates its cursor/exit. The region proof is reused from M1. This establishes
neither the whole loop nor permissions (Effects.All erases access requests). -/
theorem next_segment (n : Names) (o : Offsets) (d : Leanux.WG.Device)
    (s : MachineData) (next : UInt64)
    (related : Corresponds n o s.dmem d)
    (read : word s.dmem "loop.next" (s.regs.rbx.toNat + 8) 8 = .ok next.toNat) :
    (Lookup.run Image.Lookup.r63 0x63 s).All (fun t =>
      Corresponds n o t.data.dmem d ∧
      t.data.regs = {s.regs with rbx := next} ∧
      t.pc = if next = 0 then Image.Lookup.entry + 0x6c else Image.Lookup.entry + 0x34) := by
  have loaded := word_loadInt s.dmem "loop.next" (s.regs.rbx.toNat + 8) 8 next.toNat read
  have address : BitVec.ofNat 64 (s.regs.rbx.toNat + 8) = s.regs.rbx.toBitVec + 8 := by
    simp only [BitVec.ofNat_add, UInt64.toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rfl
  rw [address] at loaded
  refine Binary.all_mono _ _ _ ?_ (Lookup.next_entry s next loaded)
  intro t result
  exact ⟨by simpa only [result.2.1] using related, result.1, result.2.2⟩

#print axioms word_loadInt
#print axioms next_segment
end Binary.Pair
