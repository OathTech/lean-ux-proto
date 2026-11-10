import C2CutInterfaces
import FiniteExecution
import HistoryGuard
import CanonicalLoads

/-! Work package 3 of result C2: representation, the mirror link, first exits and the
witness (`WindowMapped` to `WitnessStart` of `C2CutInterfaces`). Brief:
packets/c2/proof/WP3.md.

One file: the lakefile lists every module of the package as a root and is not edited by
a work package, so a module imported from this root that is not itself a root cannot be
built; the sections below would otherwise be files of their own. -/

/-! Work package 3 of result C2, first exits: an `Eventually` proof that every execution
from `s` reaches an exit first with `P` against an actual first exit
(`FirstExitDetermined`, `FirstExitExists`). -/
namespace Binary.C2
open Binary TrustBase Leanux
local instance : Labels := Binary.Image.linkedLabels

/-- A proved instruction step holds of each actual successor. -/
theorem effects_successor (effects : Effects) (post : MachineState → Prop)
    (run : effects.All post) (t : MachineState) (next : EffectSuccessor effects t) : post t := by
  induction effects with
  | done s => exact next ▸ run
  | unimplemented _ => exact False.elim run
  | gp_unaligned _ _ => exact False.elim run
  | nonmem_load => exact False.elim run
  | nonmem_store => exact False.elim run
  | undefined continuation ih =>
    obtain ⟨value, rest⟩ := next
    exact ih value (run value) rest
  | require_read_access _ _ continuation ih | require_write_access _ _ continuation ih
  | require_exec_access _ continuation ih =>
    exact ih () run next

theorem instruction_successor (fetch : Int64 → Option Decoded) (s t : MachineState)
    (post : MachineState → Prop) (run : instructionStep fetch s post)
    (next : InstructionSuccessor fetch s t) : post t := by
  obtain ⟨decoded, fetched, _, successor⟩ := next
  unfold instructionStep at run
  simp only [fetched] at run
  exact effects_successor _ post run.2 t successor

/-- An actual history that continues past a prefix continues it by an actual successor
of the prefix's last state. -/
theorem actual_successor {fetch : Int64 → Option Decoded} {s : MachineState}
    {history : List MachineState} (actual : ActualHistory fetch s history) :
    ∀ (front : List MachineState) (current next : MachineState) (rest : List MachineState),
      history = front ++ next :: rest → front.getLast? = some current →
      InstructionSuccessor fetch current next := by
  induction actual with
  | start =>
    intro front current next rest equal last
    cases front with
    | nil => simp at last
    | cons a front => cases front <;> simp at equal
  | @snoc history current' next' prior last' successor ih =>
    intro front current next rest equal last
    rcases List.eq_nil_or_concat rest with rfl | ⟨rest', final, rfl⟩
    · have split : history = front ∧ next' = next := by
        have := List.append_inj' equal rfl
        exact ⟨this.1, by simpa using this.2⟩
      obtain ⟨rfl, rfl⟩ := split
      rw [last'] at last
      cases last
      exact successor
    · have equal' : history ++ [next'] = (front ++ next :: rest') ++ [final] := by
        simpa [List.concat_eq_append, List.append_assoc] using equal
      have := List.append_inj' equal' rfl
      exact ih front current next rest' this.1 last

/-- The induction behind `FirstExitDetermined`: a proof from an executed state whose
history is a prefix of an actual history ending at its first exit speaks of that exit. -/
theorem first_exit_of_prefix (fetch : Int64 → Option Decoded) (s t : MachineState)
    (P : MachineState → Prop) (whole : List MachineState)
    (actual : ActualHistory fetch s whole) (ends : whole.getLast? = some t)
    (exit : t.pc ∈ exits) (first : ∀ u ∈ whole.dropLast, u.pc ∉ exits)
    (e : Executed)
    (run : Eventually (historyStep fetch)
      (fun e => e.machine.pc ∈ exits ∧ (∀ u ∈ e.history.dropLast, u.pc ∉ exits) ∧ P e.machine) e) :
    e.history.getLast? = some e.machine → (∃ rest, whole = e.history ++ rest) → P t := by
  induction run with
  | done e post =>
    rintro last ⟨rest, equal⟩
    cases rest with
    | nil =>
      rw [List.append_nil] at equal
      rw [equal, last] at ends
      cases ends
      exact post.2.2
    | cons next rest =>
      exfalso
      obtain ⟨front, split⟩ := List.getLast?_eq_some_iff.mp last
      apply first e.machine _ post.1
      rw [equal, List.dropLast_append_of_ne_nil (by simp), split]
      simp
  | step e mid step branches ih =>
    rintro last ⟨rest, equal⟩
    cases rest with
    | nil =>
      exfalso
      rw [List.append_nil] at equal
      rw [equal, last] at ends
      cases ends
      obtain ⟨next, reached⟩ := Callback.instruction_witness step
      obtain ⟨leaf, post, tail, recorded⟩ := Callback.history_witness (branches _ reached)
      obtain ⟨front, split⟩ := List.getLast?_eq_some_iff.mp last
      apply post.2.1 e.machine _ exit
      rw [recorded]
      change e.machine ∈ ((e.history ++ [next]) ++ tail).dropLast
      rw [split]
      cases tail with
      | nil => simp
      | cons a tail =>
        rw [List.dropLast_append_of_ne_nil (by simp)]
        simp
    | cons next rest =>
      have successor := actual_successor actual e.history e.machine next rest equal last
      have reached := instruction_successor fetch e.machine next _ step successor
      exact ih _ reached (by simp) ⟨rest, by simpa using equal⟩

theorem first_exit_determined : FirstExitDetermined := by
  rintro fetch s t P run ⟨whole, actual, ends, exit, first⟩
  refine first_exit_of_prefix fetch s t P whole actual ends exit first ⟨s, [s]⟩ run rfl ?_
  have starts : ∀ {history}, ActualHistory fetch s history → ∃ rest, history = [s] ++ rest := by
    intro history h
    induction h with
    | start => exact ⟨[], rfl⟩
    | @snoc _ _ next _ _ _ ih =>
      obtain ⟨rest, equal⟩ := ih
      exact ⟨rest ++ [next], by rw [equal]; simp⟩
  exact starts actual

theorem first_exit_exists : FirstExitExists := by
  intro fetch s P run
  have traced := eventually_actual fetch s _ ⟨s, [s]⟩ run .start rfl
  have ended := history_last fetch _ ⟨s, [s]⟩ rfl traced
  obtain ⟨leaf, ⟨⟨⟨exit, first, holds⟩, actual⟩, last⟩, _⟩ := Callback.history_witness ended
  exact ⟨leaf.machine, ⟨leaf.history, actual, last, exit, first⟩, holds⟩

#print axioms first_exit_determined
#print axioms first_exit_exists
end Binary.C2

/-! ## Representation

`Layouts.ReplayFields` against `WindowAt`, and both against the 1032 window bytes. -/
namespace Binary.C2
open Binary TrustBase Leanux
local instance : Labels := Binary.Image.linkedLabels

theorem allSome_of_mapped : ∀ (xs : List (Option UInt8)),
    (∀ x ∈ xs, x.isSome = true) → ∃ ys, xs.allSome = some ys
  | [], _ => ⟨[], rfl⟩
  | none :: _, mapped => by simpa using mapped none (by simp)
  | some x :: xs, mapped => by
    obtain ⟨ys, rest⟩ := allSome_of_mapped xs (fun y hy => mapped y (by simp [hy]))
    have rest' : List.mapM id xs = some ys := rest
    exact ⟨x :: ys, by simp [List.allSome, List.mapM_cons, rest']⟩

theorem mapped_of_allSome : ∀ (xs : List (Option UInt8)) (ys : List UInt8),
    xs.allSome = some ys → ∀ x ∈ xs, x.isSome = true
  | [], _, _ => by simp
  | none :: _, ys, read => by simp [List.allSome, List.mapM_cons] at read
  | some x :: xs, ys, read => by
    cases tail : xs.allSome with
    | none =>
      have tail' : List.mapM id xs = none := tail
      simp [List.allSome, List.mapM_cons, tail'] at read
    | some rest =>
      intro y hy
      rcases List.mem_cons.mp hy with rfl | inside
      · rfl
      · exact mapped_of_allSome xs rest tail y inside

/-- A load reads exactly its bytes: mapped bytes give a value. -/
theorem loadInt_of_mapped (m : Mem 64) (a : BitVec 64) (n : Nat)
    (mapped : ∀ i < n, (m.get? (a + .ofNat 64 i)).isSome = true) :
    ∃ v, m.loadInt a n = some v := by
  obtain ⟨ys, read⟩ := allSome_of_mapped ((List.range n).map fun i => m.get? (a + .ofNat 64 i))
    (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact mapped i (List.mem_range.mp hi))
  refine ⟨Int.ofBytes ys, ?_⟩
  unfold Mem.loadInt Mem.loadBytes
  rw [read]
  rfl

/-- A load that gives a value read mapped bytes. -/
theorem mapped_of_loadInt (m : Mem 64) (a : BitVec 64) (n : Nat) (v : Int)
    (read : m.loadInt a n = some v) :
    ∀ i < n, (m.get? (a + .ofNat 64 i)).isSome = true := by
  intro i hi
  cases bytes : m.loadBytes a n with
  | none => simp [Mem.loadInt, bytes] at read
  | some ys =>
    exact mapped_of_allSome _ ys bytes _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

/-- A load depends only on its bytes. -/
theorem loadInt_congr (m m' : Mem 64) (a : BitVec 64) (n : Nat)
    (same : ∀ i < n, m.get? (a + .ofNat 64 i) = m'.get? (a + .ofNat 64 i)) :
    m.loadInt a n = m'.loadInt a n := by
  unfold Mem.loadInt Mem.loadBytes
  congr 2
  exact List.map_congr_left fun i hi => same i (List.mem_range.mp hi)

/-- A loaded quadword is its own 64-bit value. -/
theorem load_word (m : Mem 64) (a : BitVec 64) (v : Int) (read : m.loadInt a 8 = some v) :
    v = ((BitVec.ofNat 64 v.toNat).toNat : Int) ∧ v.toNat < 2 ^ 64 := by
  obtain ⟨low, high⟩ := loadInt_range m a 8 v read
  have high' : v < 2 ^ 64 := by simpa using high
  refine ⟨?_, by omega⟩
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Byte `i` of the counter field is byte `i` of the window. -/
theorem counter_byte (base : BitVec 64) (i : Nat) :
    base + .ofNat 64 Layouts.replay_counter + .ofNat 64 i = base + .ofNat 64 i := by
  simp [Layouts.replay_counter]

/-- Byte `i` of bitmap word `j` is byte `8 + 8 j + i` of the window. -/
theorem word_byte (base : BitVec 64) (j i : Nat) :
    base + .ofNat 64 (Layouts.replay_backtrack + j * Layouts.replayWordBytes) + .ofNat 64 i =
      base + .ofNat 64 (8 + j * 8 + i) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rfl

theorem counter_inside (kp : BitVec 64) (i : Nat) (hi : i < 8) :
    windowBytes kp (windowBase kp + .ofNat 64 Layouts.replay_counter + .ofNat 64 i) :=
  ⟨i, by simp only [Layouts.replaySize]; omega, counter_byte _ i⟩

theorem word_inside (kp : BitVec 64) (j i : Nat) (hj : j < Layouts.replayWords) (hi : i < 8) :
    windowBytes kp (windowBase kp +
      .ofNat 64 (Layouts.replay_backtrack + j * Layouts.replayWordBytes) + .ofNat 64 i) :=
  ⟨8 + j * 8 + i, by simp only [Layouts.replaySize, Layouts.replayWords] at hj ⊢; omega,
    word_byte _ j i⟩

theorem window_mapped : WindowMapped := by
  intro m kp mapped
  have counter : ∃ v, m.loadInt (windowBase kp + .ofNat 64 Layouts.replay_counter) 8 = some v :=
    loadInt_of_mapped m _ 8 (fun i hi => mapped _ (counter_inside kp i hi))
  have words : ∀ j, j < Layouts.replayWords → ∃ v, m.loadInt (windowBase kp +
      .ofNat 64 (Layouts.replay_backtrack + j * Layouts.replayWordBytes)) 8 = some v :=
    fun j hj => loadInt_of_mapped m _ 8 (fun i hi => mapped _ (word_inside kp j i hj hi))
  let w : Window :=
    { counter := .ofNat 64
        ((m.loadInt (windowBase kp + .ofNat 64 Layouts.replay_counter) 8).getD 0).toNat
      words := fun j => .ofNat 64 ((m.loadInt (windowBase kp +
        .ofNat 64 (Layouts.replay_backtrack + j * Layouts.replayWordBytes)) 8).getD 0).toNat }
  have first : m.loadInt (windowBase kp + .ofNat 64 Layouts.replay_counter) 8 =
      some (w.counter.toNat : Int) := by
    obtain ⟨v, read⟩ := counter
    have value : w.counter = .ofNat 64 v.toNat := by simp only [w, read, Option.getD_some]
    rw [value, ← (load_word m _ v read).1]
    exact read
  have rest : ∀ j, j < Layouts.replayWords → m.loadInt (windowBase kp +
      .ofNat 64 (Layouts.replay_backtrack + j * Layouts.replayWordBytes)) 8 =
        some ((w.words j).toNat : Int) := by
    intro j hj
    obtain ⟨v, read⟩ := words j hj
    have value : w.words j = .ofNat 64 v.toNat := by simp only [w, read, Option.getD_some]
    rw [value, ← (load_word m _ v read).1]
    exact read
  exact ⟨w, first, rest⟩

theorem window_of_fields : WindowOfFields := by
  rintro m base c ⟨counter, size, words⟩
  refine ⟨?_, ?_⟩
  · have fit := (load_word m _ _ counter).2
    rw [counter]
    simp only [ofCounter, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by simpa using fit)]
  · intro j hj
    have hj' : j < c.backtrack.size := size ▸ hj
    have read := words j hj'
    have fit := (load_word m _ _ read).2
    rw [read]
    simp only [ofCounter, BitVec.toNat_ofNat, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hj', Option.getD_some]
    rw [Nat.mod_eq_of_lt (by simpa using fit)]

#print axioms window_mapped
#print axioms window_of_fields
end Binary.C2
