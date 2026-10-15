import PeerCountPhase
import PeerReturnHistory

namespace Binary.PeerCountPhase
open PeerGet

/-- Every prefix of the exact increment region, including the two
    non-cut successors before CMPXCHG. -/
theorem scan_increment_prefix (seed : Option Pending) (body : MachineData) (af : Bool) (n : Nat) :
    scan seed ((⟨body, Image.PeerGet.entry+0x44⟩ :: incrementStates body af).take n) =
      if n ≤ 3 then seed else
        some ⟨body.regs.r13.toBitVec, body.regs.get (.low .rbp .W32)⟩ := by
  cases n with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n => cases n with
      | zero => simp [incrementStates, scan, edge, Image.PeerGet.entry]
      | succ n => cases n with
        | zero => simp [incrementStates, scan, edge, Image.PeerGet.entry]
        | succ n =>
          have first : edge seed ⟨body, Image.PeerGet.entry+0x44⟩
              ⟨incLea body, Image.PeerGet.entry+0x48⟩ = seed := by
            apply edge_ordinary <;> simp [Image.PeerGet.entry]
          have second : edge seed ⟨incLea body, Image.PeerGet.entry+0x48⟩
              ⟨incMove body, Image.PeerGet.entry+0x4a⟩ = seed := by
            apply edge_ordinary <;> simp [Image.PeerGet.entry]
          simp only [incrementStates, List.take_succ_cons, scan, first, second, increment_edge]
          have stable := scan_ordinary
            (some ⟨body.regs.r13.toBitVec, body.regs.get (.low .rbp .W32)⟩)
            ((⟨incCompare body, Image.PeerGet.entry+0x4f⟩ ::
              [⟨incSet body, Image.PeerGet.entry+0x53⟩,
               ⟨incXor body af, Image.PeerGet.entry+0x55⟩,
               ⟨incCopy body af, Image.PeerGet.entry+0x58⟩,
               ⟨incFinal body af, Image.PeerGet.entry+0x5b⟩]).take (n+1))
            (ordinary_take _ _ (by
              intro s member
              simp only [List.dropLast_cons_cons, List.dropLast_singleton,
                List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl | rfl | rfl <;>
                constructor <;> simp [Image.PeerGet.entry]))
          simpa only [List.take_succ_cons, show ¬n+1+1+1+1 ≤ 3 by omega, ite_false] using stable

/-- RET clears the pending phase only in its successor, never at the RET
    correspondence state itself. -/
theorem scan_return_prefix (seed : Option Pending) (body : MachineData)
    (bx bp r12 r13 r14 r15 ra : UInt64) (n : Nat) :
    scan seed ((⟨body, Image.PeerGet.entry+0xa2⟩ ::
      restoreStates body bx bp r12 r13 r14 r15 ra).take n) =
        if n ≤ 8 then seed else none := by
  cases n with
  | zero => rfl
  | succ n => cases n with
    | zero => rfl
    | succ n => cases n with
      | zero => simp [restoreStates, scan, edge, Image.PeerGet.entry]
      | succ n => cases n with
        | zero => simp [restoreStates, scan, edge, Image.PeerGet.entry]
        | succ n => cases n with
          | zero => simp [restoreStates, scan, edge, Image.PeerGet.entry]
          | succ n => cases n with
            | zero => simp [restoreStates, scan, edge, Image.PeerGet.entry]
            | succ n => cases n with
              | zero => simp [restoreStates, scan, edge, Image.PeerGet.entry]
              | succ n => cases n with
                | zero => simp [restoreStates, scan, edge, Image.PeerGet.entry]
                | succ n => cases n with
                  | zero => simp [restoreStates, scan, edge, Image.PeerGet.entry]
                  | succ n => simp [restoreStates, scan, edge, Image.PeerGet.entry]

#print axioms scan_increment_prefix
#print axioms scan_return_prefix

theorem returning_history (history : List MachineState) (body : MachineData)
    (bx bp r12 r13 r14 r15 ra : UInt64)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0xa2⟩) :
    ReturningExtension history (history ++ restoreStates body bx bp r12 r13 r14 r15 ra) := by
  refine ⟨restoreStates body bx bp r12 r13 r14 r15 ra, by simp [restoreStates], rfl, ?_⟩
  intro seed n
  rw [scan_append _ _ _ _ last]
  have phase := scan_return_prefix (scan seed history) body bx bp r12 r13 r14 r15 ra (n+1)
  simpa [List.take_succ_cons, show n+1 ≤ 8 ↔ n < 8 by omega,
    restoreStates, List.length_cons, List.length_nil] using phase

#print axioms returning_history

/-- The single actual count-update region inside an executed helper. The
    boundary is retained as an actual history prefix and last state; later
    callbacks preserve its pending operand until the final RET. -/
def IncrementingReturn (before after : List MachineState) (address : Address) (old : BitVec 32) : Prop :=
  ∃ body history af,
    StableExtension before history ∧
    history.getLast? = some ⟨body, Image.PeerGet.entry+0x44⟩ ∧
    body.regs.r13.toBitVec = address ∧ body.regs.get (.low .rbp .W32) = old ∧
    ReturningExtension (history ++ incrementStates body af) after

/-- The same phase witness at a specified prefix, used to tie it to the
    old/new memory-frame partition rather than choosing two boundaries. -/
def IncrementingReturnAt (before boundary after : List MachineState)
    (address : Address) (old : BitVec 32) : Prop :=
  ∃ body af,
    StableExtension before boundary ∧
    boundary.getLast? = some ⟨body, Image.PeerGet.entry+0x44⟩ ∧
    body.regs.r13.toBitVec = address ∧ body.regs.get (.low .rbp .W32) = old ∧
    ReturningExtension (boundary ++ incrementStates body af) after

theorem IncrementingReturnAt.forget {before boundary after address old}
    (run : IncrementingReturnAt before boundary after address old) :
    IncrementingReturn before after address old := by
  obtain ⟨body, af, stable, last, addr, count, returned⟩ := run
  exact ⟨body, boundary, af, stable, last, addr, count, returned⟩

theorem StableExtension.incrementing_at {first middle boundary last : List MachineState} {address old}
    (neutral : StableExtension first middle)
    (rest : IncrementingReturnAt middle boundary last address old) :
    IncrementingReturnAt first boundary last address old := by
  obtain ⟨body, af, earlier, cursor, addr, count, returned⟩ := rest
  exact ⟨body, af, neutral.trans earlier, cursor, addr, count, returned⟩

theorem StableExtension.incrementing {first middle last : List MachineState} {address old}
    (neutral : StableExtension first middle) (rest : IncrementingReturn middle last address old) :
    IncrementingReturn first last address old := by
  obtain ⟨body, history, af, earlier, cursor, addr, count, returned⟩ := rest
  exact ⟨body, history, af, neutral.trans earlier, cursor, addr, count, returned⟩

#print axioms StableExtension.incrementing
#print axioms IncrementingReturnAt.forget
#print axioms StableExtension.incrementing_at
end Binary.PeerCountPhase
