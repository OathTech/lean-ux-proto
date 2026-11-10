import C2CutInterfaces

/-! Work package 2 of result C2: a history-keeping `region_eventually`.

The landed `region_eventually` gives an `instructionStep` execution and forgets the
states passed through. The cut predicates need `Quiet` (no state so far at an exit) and
`AtExit.first`, so here the same induction on `LaidOut` is done over `historyStep`,
recording that every state added to the history, the last one apart, is at the address
of an instruction of the region. Generic: nothing here mentions the range. -/
namespace Binary

/-- The addresses of the instructions of a region laid out at `pc`. -/
def regionStarts (pc : Int64) : List (Kraken.Sized Directive) → List Int64
  | [] => []
  | i :: rest => pc :: regionStarts (pc + .ofNat i.size) rest

/-- What a region adds to a history: the states from the start on are `mid` followed by
the final state, and every state of `mid` is at an instruction of the region. -/
def RegionTrail (pc : Int64) (code : List (Kraken.Sized Directive)) (s : MachineState)
    (history : List MachineState) (e : Executed) : Prop :=
  ∃ added mid, e.history = history ++ added ∧ s :: added = mid ++ [e.machine] ∧
    ∀ u ∈ mid, u.pc ∈ regionStarts pc code

/-- Region symbolic execution entails a recorded execution of each fetched instruction,
and the states it records are at the region's instructions. -/
theorem region_history [Labels] {fetch pc code}
    (layout : LaidOut fetch pc code) (s : MachineData) (history : List MachineState)
    (P : MachineState → Prop)
    (run : (Directives.interp code s pc (fun p d => .done ⟨d, p⟩)).All P) :
    Eventually (historyStep fetch)
      (fun e => P e.machine ∧ RegionTrail pc code ⟨s, pc⟩ history e) ⟨⟨s, pc⟩, history⟩ := by
  induction layout generalizing s history with
  | nil pc => exact .done _ ⟨run, [], [], by simp, by simp, by simp⟩
  | cons pc i n tail positive here mono rest ih =>
    apply step_cps
    simp only [historyStep, instructionStep, here]
    refine ⟨positive, ?_⟩
    apply mono s ⟨pc, pc + .ofNat n⟩
      (fun d => Directives.interp tail d (pc + .ofNat n) (fun p d => .done ⟨d, p⟩))
      _ (fun p d => .done ⟨d, p⟩) _ P _
    · intro d h
      change Eventually _ _ _
      refine eventually_weaken (historyStep fetch) _ _ _ ?_ (ih d _ h)
      rintro e ⟨post, added, mid, recorded, trail, inside⟩
      refine ⟨post, (⟨d, pc + .ofNat n⟩ : MachineState) :: added, (⟨s, pc⟩ : MachineState) :: mid, ?_, ?_, ?_⟩
      · simpa only [List.append_assoc, List.singleton_append] using recorded
      · simp only [List.cons_append, trail]
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (inside u hu)
    · intro p d h
      change Eventually _ _ _
      exact .done _ ⟨h, [(⟨d, p⟩ : MachineState)], [(⟨s, pc⟩ : MachineState)], rfl, rfl, by
        intro u hu
        rw [List.mem_singleton.mp hu]
        exact List.mem_cons_self⟩
    · exact run

/-- Every state of the history after a region is in the history before it, at an
instruction of the region, or the final state. -/
theorem RegionTrail.mem {pc code s history e} (trail : RegionTrail pc code s history e)
    (u : MachineState) (hu : u ∈ e.history) :
    u ∈ history ∨ u.pc ∈ regionStarts pc code ∨ u = e.machine := by
  obtain ⟨added, mid, recorded, split, inside⟩ := trail
  rw [recorded] at hu
  rcases List.mem_append.mp hu with old | new
  · exact .inl old
  · have : u ∈ mid ++ [e.machine] := split ▸ List.mem_cons_of_mem _ new
    rcases List.mem_append.mp this with m | last
    · exact .inr (.inl (inside u m))
    · exact .inr (.inr (List.mem_singleton.mp last))

/-- Every state of the history after a region but its last is in the history before it
or at an instruction of the region. -/
theorem RegionTrail.mem_dropLast {pc code s history e} (trail : RegionTrail pc code s history e)
    (u : MachineState) (hu : u ∈ e.history.dropLast) :
    u ∈ history ∨ u.pc ∈ regionStarts pc code := by
  obtain ⟨added, mid, recorded, split, inside⟩ := trail
  rw [recorded] at hu
  cases added with
  | nil =>
    rw [List.append_nil] at hu
    exact .inl (List.dropLast_subset _ hu)
  | cons a rest =>
    rw [List.dropLast_append_of_ne_nil (by simp)] at hu
    rcases List.mem_append.mp hu with old | new
    · exact .inl old
    · right
      apply inside
      have drop := congrArg List.dropLast split
      rw [List.dropLast_concat, List.dropLast_cons_of_ne_nil (by simp)] at drop
      rw [← drop]
      exact List.mem_cons_of_mem _ new

#print axioms region_history
#print axioms RegionTrail.mem
#print axioms RegionTrail.mem_dropLast
end Binary
