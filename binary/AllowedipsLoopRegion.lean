import RegionExecution
import History

namespace Binary.AllowedipsLoop

/-- Starts of the actual decoded instructions in a straight-line region. -/
def regionPCs (pc : Int64) : List (Kraken.Sized Directive) → List Int64
  | [] => []
  | i :: rest => pc :: regionPCs (pc + .ofNat i.size) rest

theorem layout_take [Labels] {fetch pc code}
    (layout : LaidOut fetch pc code) (n : Nat) : LaidOut fetch pc (code.take n) := by
  induction layout generalizing n with
  | nil pc => simpa only [List.take_nil] using (LaidOut.nil (fetch := fetch) pc)
  | cons pc i size tail positive here mono rest ih =>
    cases n with
    | zero => exact .nil pc
    | succ n => exact .cons pc i size (tail.take n) positive here mono (ih n)

/-- Endpoint symbolic execution retains a real path whose nonterminal PCs
are instruction starts in this region. This permits all-cut framing of
regions with no interior cut, without assuming intermediate memories. -/
theorem region_history [Labels] {fetch pc code}
    (layout : LaidOut fetch pc code) (s : MachineData) (P : MachineState → Prop)
    (run : (Directives.interp code s pc (fun p d => .done ⟨d,p⟩)).All P)
    (front : List MachineState) :
    Eventually (historyStep fetch) (fun t => P t.machine ∧
      ∃ localPath, localPath.head? = some ⟨s,pc⟩ ∧
        localPath.getLast? = some t.machine ∧ t.history = front ++ localPath ∧
        ∀ q ∈ localPath.dropLast, q.pc ∈ regionPCs pc code ∧
          (q = ⟨s,pc⟩ ∨ q.pc ∈ (regionPCs pc code).tail))
      ⟨⟨s,pc⟩,front ++ [⟨s,pc⟩]⟩ := by
  induction layout generalizing s front with
  | nil pc =>
    exact .done _ ⟨run, [⟨s,pc⟩], rfl, rfl, rfl, by simp⟩
  | cons pc i n tail positive here mono rest ih =>
    apply step_cps
    simp only [historyStep, instructionStep, here]
    refine ⟨positive, ?_⟩
    apply mono s ⟨pc,pc + .ofNat n⟩
      (fun d => Directives.interp tail d (pc + .ofNat n) (fun p d => .done ⟨d,p⟩))
      _ (fun p d => .done ⟨d,p⟩) _ P _
    · intro d good
      have recursive := ih d good (front ++ [⟨s,pc⟩])
      apply eventually_weaken (historyStep fetch) _ _ _ _ recursive
      rintro t ⟨post,path,head,last,recorded,inside⟩
      have nonempty : path ≠ [] := by intro empty; rw [empty] at head; cases head
      refine ⟨post, ⟨s,pc⟩ :: path, rfl, ?_, ?_, ?_⟩
      · simp only [List.getLast?_cons, last, Option.getD_some]
      · simpa only [List.append_assoc, List.singleton_append] using recorded
      · intro q member
        rw [List.dropLast_cons_of_ne_nil nonempty] at member
        rcases List.mem_cons.mp member with eq | member
        · subst q; exact ⟨.head _, .inl rfl⟩
        · exact ⟨.tail _ (inside q member).1, .inr (inside q member).1⟩
    · intro target d good
      exact .done _ ⟨good, [⟨s,pc⟩,⟨d,target⟩], rfl, rfl,
        by simp only [List.append_assoc, List.singleton_append], by
          intro q member
          simp only [List.dropLast_cons_cons, List.dropLast_singleton, List.mem_singleton] at member
          subst q
          exact ⟨.head _, .inl rfl⟩⟩
    · exact run

/-- Observation of a real path is empty when each executed source PC is
proved silent. The terminal PC is not executed by this segment. -/
theorem observe_silent {Error Checkpoint : Type}
    (edge : MachineState → MachineState → Except Error (List Checkpoint))
    (path : List MachineState)
    (silent : ∀ s ∈ path.dropLast, ∀ t, edge s t = .ok []) :
    observeHistory edge path = .ok [] := by
  induction path with
  | nil => rfl
  | cons s rest ih =>
    cases rest with
    | nil => rfl
    | cons t rest =>
      change (do
        let first ← edge s t
        let later ← observeHistory edge (t :: rest)
        pure (first ++ later)) = .ok []
      rw [silent s (by simp) t, ih (by
        intro q member next
        exact silent q (by simp only [List.dropLast_cons_cons, List.mem_cons]; exact .inr member) next)]
      rfl

/-- Scalar regions with no interior cut inherit every required cut frame
from their initial and final states. No claim is made about unobserved
intermediate memories; all instructions still execute under Kraken. -/
theorem quiet_region [Labels] {Error Checkpoint : Type} {fetch pc code}
    (layout : LaidOut fetch pc code) (s : MachineData)
    (P Frame : MachineState → Prop)
    (run : (Directives.interp code s pc (fun p d => .done ⟨d,p⟩)).All
      (fun t => P t ∧ Frame t))
    (initial : Frame ⟨s,pc⟩)
    (edge : MachineState → MachineState → Except Error (List Checkpoint))
    (cut : Int64 → Prop)
    (silent : ∀ address ∈ regionPCs pc code, ∀ before after,
      before.pc = address → edge before after = .ok [])
    (noInterior : ∀ address ∈ (regionPCs pc code).tail, ¬cut address)
    (front : List MachineState) :
    Eventually (historyStep fetch) (fun t => P t.machine ∧ Frame t.machine ∧
      ∃ path, path.head? = some ⟨s,pc⟩ ∧ path.getLast? = some t.machine ∧
        t.history = front ++ path ∧ observeHistory edge path = .ok [] ∧
        ∀ q ∈ path, cut q.pc → Frame q)
      ⟨⟨s,pc⟩, front ++ [⟨s,pc⟩]⟩ := by
  apply eventually_weaken (historyStep fetch) _ _ _ _ (region_history layout s _ run front)
  rintro t ⟨⟨post,frame⟩,path,head,last,recorded,inside⟩
  refine ⟨post,frame,path,head,last,recorded,?_,?_⟩
  · apply observe_silent
    intro before member after
    exact silent before.pc (inside before member).1 before after rfl
  · intro q member atCut
    have restore := Binary.history_restore last
    rw [← restore] at member
    rcases List.mem_append.mp member with prior | endpoint
    · rcases (inside q prior).2 with eq | interior
      · exact eq.symm ▸ initial
      · exact False.elim (noInterior q.pc interior atCut)
    · exact (List.mem_singleton.mp endpoint).symm ▸ frame

#print axioms region_history
#print axioms observe_silent
#print axioms quiet_region
end Binary.AllowedipsLoop
