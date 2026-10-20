import History

namespace Binary

/-- A possible successor of the actual instruction effects, retaining all
    undefined choices. Faults and unimplemented instructions have none. -/
def EffectSuccessor : Effects → MachineState → Prop
  | .done s, t => t = s
  | .unimplemented _, _ | .gp_unaligned .., _ | .nonmem_load .., _ | .nonmem_store .., _ => False
  | @Effects.undefined α _ next, t => ∃ value : α, EffectSuccessor (next value) t
  | .require_read_access _ _ next, t => EffectSuccessor (next ()) t
  | .require_write_access _ _ next, t => EffectSuccessor (next ()) t
  | .require_exec_access _ next, t => EffectSuccessor (next ()) t

def InstructionSuccessor [Labels] (fetch : Int64 → Option Decoded) (s t : MachineState) : Prop :=
  ∃ decoded, fetch s.pc = some decoded ∧ decoded.size > 0 ∧
    EffectSuccessor (decoded.instruction.interp s.data ⟨s.pc, s.pc + .ofNat decoded.size⟩
      (fun d => .done ⟨d, s.pc + .ofNat decoded.size⟩) (fun pc d => .done ⟨d, pc⟩)) t

/-- Finite actual prefixes, independent of termination, a mirror result or R. -/
inductive ActualHistory [Labels] (fetch : Int64 → Option Decoded) (initial : MachineState) :
    List MachineState → Prop
  | start : ActualHistory fetch initial [initial]
  | snoc {history current next} : ActualHistory fetch initial history →
      history.getLast? = some current → InstructionSuccessor fetch current next →
      ActualHistory fetch initial (history ++ [next])

/-- The last executed instruction is the named outer return. -/
def EndsAtReturn (returnPC : Int64) (history : List MachineState) : Prop :=
  ∃ front before after, history = front ++ [before, after] ∧ before.pc = returnPC

/-- A prefix stops at the successor of its first outer RET, if reached.
    In particular it imposes no access premise on the caller continuation. -/
def NoEarlyReturn (returnPC : Int64) (history : List MachineState) : Prop :=
  ∀ s ∈ history.dropLast.dropLast, s.pc ≠ returnPC

private theorem all_successors (effects : Effects) (post : MachineState → Prop)
    (run : effects.All post) : effects.All (fun t => EffectSuccessor effects t ∧ post t) := by
  induction effects with
  | done s => exact ⟨rfl, run⟩
  | unimplemented _ => exact False.elim run
  | gp_unaligned _ _ => exact False.elim run
  | nonmem_load => exact False.elim run
  | nonmem_store => exact False.elim run
  | undefined next ih =>
    intro value
    exact all_mono _ _ _ (fun t h => ⟨⟨value, h.1⟩, h.2⟩) (ih value (run value))
  | require_read_access _ _ next ih | require_write_access _ _ next ih | require_exec_access _ next ih =>
    exact ih () run

theorem instruction_successors [Labels] (fetch : Int64 → Option Decoded)
    (s : MachineState) (post : MachineState → Prop) (run : instructionStep fetch s post) :
    instructionStep fetch s (fun t => InstructionSuccessor fetch s t ∧ post t) := by
  unfold instructionStep at run ⊢
  cases h : fetch s.pc with
  | none => simp only [h] at run
  | some decoded =>
    simp only [h] at run ⊢
    exact ⟨run.1, all_mono _ _ _ (fun t ht => ⟨⟨decoded, h, run.1, ht.1⟩, ht.2⟩)
      (all_successors _ _ run.2)⟩

/-- Every execution proof carries its own finite actual history. The trace
    is not an extra hypothesis supplied by a proof producer. -/
theorem eventually_actual [Labels] (fetch : Int64 → Option Decoded)
    (initial : MachineState) (post : Executed → Prop) (s : Executed)
    (run : Eventually (historyStep fetch) post s)
    (history : ActualHistory fetch initial s.history)
    (last : s.history.getLast? = some s.machine) :
    Eventually (historyStep fetch) (fun t => post t ∧ ActualHistory fetch initial t.history) s := by
  induction run with
  | done s hp => exact .done s ⟨hp, history⟩
  | step s mid run _ ih =>
    apply step_cps
    apply instruction_mono fetch s.machine _ _ _ (instruction_successors fetch s.machine _ run)
    intro next hn
    exact ih ⟨next, s.history ++ [next]⟩ hn.2 (.snoc history last hn.1) (by simp)

end Binary
