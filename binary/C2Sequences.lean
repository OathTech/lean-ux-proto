import C2CutInterfaces
import FiniteExecution
import HistoryGuard
import CanonicalLoads
import MemoryBytes
import C2CutAssembly

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

theorem fields_of_window : FieldsOfWindow := by
  rintro m base w ⟨counter, words⟩
  refine ⟨counter, by simp [toCounter], ?_⟩
  intro j hj
  have hj' : j < Layouts.replayWords := by simpa [toCounter] using hj
  rw [words j hj']
  simp [toCounter]

theorem fields_fit : FieldsFit := by
  rintro m base c ⟨counter, size, words⟩
  refine ⟨by simpa using (load_word m _ _ counter).2, size, ?_⟩
  intro j hj
  simpa using (load_word m _ _ (words j hj)).2

theorem fields_retained : FieldsRetained := by
  rintro m m' kp c ⟨counter, size, words⟩ same
  refine ⟨?_, size, ?_⟩
  · rw [← counter]
    exact (loadInt_congr m m' _ 8 fun i hi => same _ (counter_inside kp i hi)).symm
  · intro j hj
    rw [← words j hj]
    exact (loadInt_congr m m' _ 8 fun i hi =>
      same _ (word_inside kp j i (size ▸ hj) hi)).symm

theorem fields_mapped : FieldsMapped := by
  rintro m kp c ⟨counter, size, words⟩ a ⟨i, hi, rfl⟩
  simp only [Layouts.replaySize] at hi
  by_cases low : i < 8
  · have := mapped_of_loadInt m _ 8 _ counter i low
    rwa [counter_byte] at this
  · have hj : (i - 8) / 8 < c.backtrack.size := by
      rw [size]; simp only [Layouts.replayWords]; omega
    have := mapped_of_loadInt m _ 8 _ (words _ hj) ((i - 8) % 8) (Nat.mod_lt _ (by omega))
    rw [word_byte] at this
    rwa [show 8 + (i - 8) / 8 * 8 + (i - 8) % 8 = i by omega] at this

#print axioms window_mapped
#print axioms window_of_fields
#print axioms fields_of_window
#print axioms fields_fit
#print axioms fields_retained
#print axioms fields_mapped
end Binary.C2

/-! Work package 3 of result C2, the mirror link: `MirrorFollowsSpec`.

The mirror's `Leanux.WG.counterValidate`, run in its own monad, is first shown to return
and store what a monad-free transcription (`mirrorResult`, unbounded `Nat` arithmetic on
the keypair's `Array Nat` bitmap) says; the transcription is then shown to be the pivot
`validate` on states that fit the machine's widths. Everything is proved from the
mirror's definition; nothing is taken from the proof tree. -/
namespace Binary.C2.Mirror
open Binary TrustBase Leanux Binary.C2

/-! ## Running the mirror's monad -/

/-- `x`, run from `wg` with any ambient state, returns `a` and leaves `wg'` (the ambient
state, i.e. the recorded decisions, is not described). -/
def Ret {α : Type} (x : WG.M α) (wg : WGWorld) (a : α) (wg' : WGWorld) : Prop :=
  ∀ amb : Ambient, ∃ amb', (x.run wg).run amb = .ok ((a, wg'), amb')

theorem Ret.pure {α : Type} (a : α) (wg : WGWorld) : Ret (pure a : WG.M α) wg a wg :=
  fun amb => ⟨amb, rfl⟩

theorem Ret.bind {α β : Type} {x : WG.M α} {f : α → WG.M β} {wg wg1 wg2 : WGWorld} {a : α} {b : β}
    (hx : Ret x wg a wg1) (hf : Ret (f a) wg1 b wg2) : Ret (x >>= f) wg b wg2 := by
  intro amb
  obtain ⟨amb1, h1⟩ := hx amb
  obtain ⟨amb2, h2⟩ := hf amb1
  refine ⟨amb2, ?_⟩
  rw [← h2]
  have e : ((x >>= f).run wg).run amb = ((x.run wg).run amb >>= fun p => ((f p.1.1).run p.1.2).run p.2) :=
    rfl
  rw [e, h1]
  rfl

theorem Ret.branch (d : Decision) (o : Bool) (wg : WGWorld) :
    Ret (Leanux.branch d o : WG.M Bool) wg o wg := fun _ => ⟨_, rfl⟩

theorem Ret.branchCmp (d : Decision) (o : Bool) (a b : Int) (wg : WGWorld) :
    Ret (Leanux.branchCmp d o a b : WG.M Bool) wg o wg := fun _ => ⟨_, rfl⟩

theorem Ret.getDev {wg : WGWorld} {d : WG.Device} (hd : wg.dev = some d) :
    Ret WG.getDev wg d wg := by
  unfold WG.getDev
  refine Ret.bind (a := wg) (fun amb => ⟨amb, rfl⟩) ?_
  rw [hd]
  exact Ret.pure d wg

theorem Ret.getKeypair {wg : WGWorld} {d : WG.Device} {kp : WG.KeypairId} {k : WG.Keypair}
    (hd : wg.dev = some d) (hk : d.keypairs.get? kp = some k) :
    Ret (WG.getKeypair kp) wg k wg := by
  unfold WG.getKeypair
  refine Ret.bind (Ret.getDev hd) ?_
  rw [hk]
  exact Ret.pure k wg

/-- The world after `setKeypair kp k`. -/
def withKeypair (wg : WGWorld) (kp : WG.KeypairId) (k : WG.Keypair) : WGWorld :=
  { wg with dev := wg.dev.map fun d => { d with keypairs := d.keypairs.insert kp k } }

theorem Ret.setKeypair (wg : WGWorld) (kp : WG.KeypairId) (k : WG.Keypair) :
    Ret (WG.setKeypair kp k) wg () (withKeypair wg kp k) :=
  fun amb => ⟨amb, rfl⟩

/-- A `for` over a list whose body always yields. -/
theorem Ret.forIn_list {β : Type} (wg : WGWorld) (f : Nat → β → WG.M (ForInStep β)) (g : β → Nat → β)
    (P : β → Prop) (hf : ∀ i b, P b → Ret (f i b) wg (.yield (g b i)) wg ∧ P (g b i)) :
    ∀ (l : List Nat) (b : β), P b → Ret (forIn l b f) wg (l.foldl g b) wg := by
  intro l
  induction l with
  | nil => intro b _; exact Ret.pure b wg
  | cons i l ih =>
    intro b hb
    rw [List.forIn_cons]
    exact Ret.bind (hf i b hb).1 (ih _ (hf i b hb).2)

theorem ret_or_branchCmp (d1 d2 : Decision) (o1 o2 : Bool) (a1 b1 a2 b2 : Int) (wg : WGWorld) :
    Ret (do
      let x ← (Leanux.branchCmp d1 o1 a1 b1 : WG.M Bool)
      if x = true then pure true else Leanux.branchCmp d2 o2 a2 b2) wg (o1 || o2) wg := by
  refine Ret.bind (Ret.branchCmp _ _ _ _ _) ?_
  cases o1
  · exact Ret.branchCmp _ _ _ _ _
  · exact Ret.pure true wg

/-! ## The transcription -/

/-- `for i in [1:n+1] do backtrack := backtrack.set! ((i + cur) % 128) 0`. -/
def clearNat (bt : Array Nat) (cur n : Nat) : Array Nat :=
  (List.range' 1 n).foldl (fun b i => b.set! ((i + cur) % 128) 0) bt

/-- `none`: rejected (the mirror returns `false` and leaves the keypair alone); otherwise
the new counter, the cleared bitmap, the word index and the bit. -/
def mirrorCore (counter : Nat) (bt : Array Nat) (theirs : Nat) : Option (Nat × Array Nat × Nat × Nat) :=
  if counter ≥ WG.REJECT_AFTER_MESSAGES + 1 ∨ theirs ≥ WG.REJECT_AFTER_MESSAGES then none
  else
    let th := theirs + 1
    if WG.COUNTER_WINDOW_SIZE + th < counter then none
    else
      let words := WG.COUNTER_BITS_TOTAL / BITS_PER_LONG
      let index := th / BITS_PER_LONG
      let next : Nat × Array Nat :=
        if th > counter then
          (th, clearNat bt (counter / BITS_PER_LONG) (min (index - counter / BITS_PER_LONG) words))
        else (counter, bt)
      some (next.1, next.2, index % words, th % BITS_PER_LONG)

/-- What `counterValidate` returns and stores, given `mirrorCore`'s result. -/
def mirrorResult (counter : Nat) (bt : Array Nat) (theirs : Nat) : Bool × WG.ReplayCounter :=
  match mirrorCore counter bt theirs with
  | none => (false, { counter, backtrack := bt })
  | some (c, b, index, bit) =>
    ((b[index]! >>> bit) % 2 == 0, { counter := c, backtrack := b.set! index (b[index]! ||| (1 <<< bit)) })

theorem clearNat_succ (bt : Array Nat) (cur n : Nat) :
    clearNat bt cur (n + 1) = (clearNat bt cur n).set! ((1 + n + cur) % 128) 0 := by
  unfold clearNat
  rw [List.range'_concat, List.foldl_append]
  simp

theorem clearNat_size (bt : Array Nat) (cur n : Nat) : (clearNat bt cur n).size = bt.size := by
  induction n with
  | zero => rfl
  | succ n ih => rw [clearNat_succ]; simpa using ih

/-- The mirror's function returns and stores `mirrorResult`. -/
theorem counterValidate_mirror (wg : WGWorld) (d : WG.Device) (kp : WG.KeypairId) (k : WG.Keypair)
    (theirs : Nat) (hd : wg.dev = some d) (hk : d.keypairs.get? kp = some k)
    (hsize : k.receivingCounter.backtrack.size = 128) :
    Ret (WG.counterValidate kp theirs) wg
      (mirrorResult k.receivingCounter.counter k.receivingCounter.backtrack theirs).1
      (match mirrorCore k.receivingCounter.counter k.receivingCounter.backtrack theirs with
        | none => wg
        | some _ => withKeypair wg kp { k with receivingCounter :=
                      (mirrorResult k.receivingCounter.counter k.receivingCounter.backtrack theirs).2 }) := by
  have hb : BITS_PER_LONG = 64 := rfl
  have hw : WG.COUNTER_BITS_TOTAL / 64 = 128 := by decide
  unfold WG.counterValidate
  refine Ret.bind (Ret.getKeypair hd hk) ?_
  dsimp only
  unfold WG.orM
  refine Ret.bind (ret_or_branchCmp _ _ _ _ _ _ _ _ _) ?_
  simp only [mirrorResult, mirrorCore, hb, hw]
  by_cases h12 : k.receivingCounter.counter ≥ WG.REJECT_AFTER_MESSAGES + 1 ∨
      theirs ≥ WG.REJECT_AFTER_MESSAGES
  · have e : (decide (k.receivingCounter.counter ≥ WG.REJECT_AFTER_MESSAGES + 1) ||
        decide (theirs ≥ WG.REJECT_AFTER_MESSAGES)) = true := by simpa using h12
    simp only [e, h12, ↓reduceIte]
    exact Ret.pure false wg
  have e : (decide (k.receivingCounter.counter ≥ WG.REJECT_AFTER_MESSAGES + 1) ||
      decide (theirs ≥ WG.REJECT_AFTER_MESSAGES)) = false := by simpa using h12
  simp only [e, h12, Bool.false_eq_true, ↓reduceIte]
  refine Ret.bind (Ret.branch _ _ _) ?_
  by_cases h3 : WG.COUNTER_WINDOW_SIZE + (theirs + 1) < k.receivingCounter.counter
  · simp only [h3, decide_true, ↓reduceIte]
    exact Ret.pure false wg
  simp only [h3, decide_false, Bool.false_eq_true, ↓reduceIte]
  refine Ret.bind (Ret.branch _ _ _) ?_
  by_cases h4 : theirs + 1 > k.receivingCounter.counter
  · simp only [h4, decide_true, ↓reduceIte]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    generalize min ((theirs + 1) / 64 - k.receivingCounter.counter / 64) 128 = N
    have hr : List.range' [1:N + 1].start [1:N + 1].size [1:N + 1].step = List.range' 1 N := by
      simp [Std.Legacy.Range.size]
    rw [hr]
    refine Ret.bind (Ret.forIn_list wg _
      (fun b i => b.set! ((i + k.receivingCounter.counter / 64) % 128) 0) (fun b => b.size = 128)
      ?_ _ _ hsize) ?_
    · intro i b hb
      refine ⟨Ret.bind (Ret.branch _ _ _) ?_, by simpa using hb⟩
      have no : ¬((i + k.receivingCounter.counter / 64) % 128 ≥ b.size) := by rw [hb]; omega
      simp only [no, ↓reduceIte]
      exact Ret.pure _ _
    have hfold : List.foldl (fun b i => b.set! ((i + k.receivingCounter.counter / 64) % 128) 0)
        k.receivingCounter.backtrack (List.range' 1 N) =
        clearNat k.receivingCounter.backtrack (k.receivingCounter.counter / 64) N := rfl
    rw [hfold]
    refine Ret.bind (Ret.branch _ _ _) ?_
    have hidx : (theirs + 1) / 64 % 128 <
        (clearNat k.receivingCounter.backtrack (k.receivingCounter.counter / 64) N).size := by
      rw [clearNat_size, hsize]; omega
    rw [Array.getElem?_eq_getElem hidx, getElem!_pos (clearNat k.receivingCounter.backtrack
      (k.receivingCounter.counter / 64) N) _ hidx]
    refine Ret.bind (Ret.setKeypair _ _ _) ?_
    exact Ret.pure _ _
  · simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hidx : (theirs + 1) / 64 % 128 < k.receivingCounter.backtrack.size := by rw [hsize]; omega
    rw [Array.getElem?_eq_getElem hidx, getElem!_pos k.receivingCounter.backtrack _ hidx]
    refine Ret.bind (Ret.setKeypair _ _ _) ?_
    exact Ret.pure _ _

/-! ## The transcription is the pivot -/

/-- A bitmap the machine can hold. -/
structure Good (b : Array Nat) : Prop where
  size : b.size = 128
  words : ∀ j (h : j < b.size), b[j] < 2 ^ 64

theorem Good.set_zero {b : Array Nat} (good : Good b) (i : Nat) : Good (b.set! i 0) := by
  refine ⟨by simpa using good.size, fun j h => ?_⟩
  have hj : j < b.size := by simpa using h
  simp only [Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds]
  split
  · omega
  · exact good.words j hj

theorem getD_set (b : Array Nat) (i j v : Nat) (hi : i < b.size) :
    (b.set! i v).getD j 0 = if j = i then v else b.getD j 0 := by
  by_cases e : j = i
  · subst e; simp [hi]
  · have e' : ¬i = j := fun h => e h.symm
    simp [e, e']

theorem clear_link (bt : Array Nat) (good : Good bt) (cur : Nat) :
    ∀ n, Good (clearNat bt cur n) ∧ ∀ j,
      clearWords (fun j => .ofNat 64 (bt.getD j 0)) (.ofNat 64 cur) n j =
        .ofNat 64 ((clearNat bt cur n).getD j 0) := by
  intro n
  induction n with
  | zero => exact ⟨good, fun j => rfl⟩
  | succ n ih =>
    obtain ⟨g, vals⟩ := ih
    have ix : ((BitVec.ofNat 64 cur + BitVec.ofNat 64 (n + 1)) &&& 127).toNat = (1 + n + cur) % 128 := by
      rw [BitVec.toNat_and, show BitVec.toNat (127 : BitVec 64) = 127 from rfl,
        Nat.and_two_pow_sub_one_eq_mod _ 7, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    rw [clearNat_succ]
    refine ⟨g.set_zero _, fun j => ?_⟩
    show (if j = ((BitVec.ofNat 64 cur + BitVec.ofNat 64 (n + 1)) &&& 127).toNat then 0
      else clearWords (fun j => BitVec.ofNat 64 (bt.getD j 0)) (BitVec.ofNat 64 cur) n j) = _
    rw [ix, vals j, getD_set _ _ _ _ (by rw [g.size]; omega)]
    split <;> rfl

/-- The test-and-set tail on a machine window that holds the bitmap `b`. -/
theorem tested_link (W : Window) (b : Array Nat) (t : BitVec 64) (index bit : Nat)
    (good : Good b) (held : ∀ j, W.words j = .ofNat 64 (b.getD j 0))
    (hi : ((t >>> 6) &&& 127).toNat = index) (hb : (t &&& 63).toNat = bit)
    (li : index < 128) (lb : bit < 64) :
    ((b[index]! >>> bit) % 2 == 0) = (tested W t).accepted ∧
    ({ counter := W.counter.toNat, backtrack := b.set! index (b[index]! ||| (1 <<< bit)) } :
      WG.ReplayCounter) = toCounter (tested W t).window := by
  have inb : index < b.size := by rw [good.size]; exact li
  have word : b[index]! = b[index] := getElem!_pos b index inb
  have wlt := good.words index inb
  have gd : ∀ j (h : j < b.size), b.getD j 0 = b[j] := fun j h => by simp [h]
  constructor
  · show _ = !(W.words ((t >>> 6) &&& 127).toNat).getLsbD (t &&& 63).toNat
    rw [hi, hb, held, gd index inb, word, BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq,
      Nat.shiftRight_eq_div_pow]
    have := Nat.mod_two_eq_zero_or_one (b[index] / 2 ^ bit)
    rcases this with h | h <;> simp [h, lb]
  · show _ = WG.ReplayCounter.mk _ _
    refine congrArg (WG.ReplayCounter.mk _) ?_
    apply Array.ext
    · rw [Array.size_ofFn]
      simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
      exact good.size
    · intro j h1 h2
      have hj : j < b.size := by simpa using h1
      rw [Array.getElem_ofFn]
      show _ = ((setBit W t).words j).toNat
      unfold setBit
      simp only [hi, hb]
      simp only [Array.set!_eq_setIfInBounds]
      rw [Array.getElem_setIfInBounds]
      have small := good.words j hj
      by_cases e : index = j
      · subst e
        simp only [↓reduceIte]
        rw [held, gd index inb, word, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft]
        have p : (1 : Nat) <<< bit < 2 ^ 64 := by
          rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by omega) lb
        rw [show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt p, Nat.mod_eq_of_lt small]
      · have e' : ¬j = index := fun h => e h.symm
        simp only [e, e', ↓reduceIte]
        rw [held, gd j hj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

theorem toCounter_ofCounter (c : WG.ReplayCounter) (fits : Fits c) : toCounter (ofCounter c) = c := by
  show WG.ReplayCounter.mk _ _ = c
  cases c with
  | mk counter backtrack =>
    have hc : counter < 2 ^ 64 := fits.counter
    have hs : backtrack.size = 128 := fits.size
    rw [WG.ReplayCounter.mk.injEq]
    refine ⟨?_, ?_⟩
    · show (BitVec.ofNat 64 counter).toNat = counter
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
    · apply Array.ext
      · rw [Array.size_ofFn]; exact hs.symm
      · intro j h1 h2
        rw [Array.getElem_ofFn]
        show (BitVec.ofNat 64 (backtrack.getD j 0)).toNat = _
        have : backtrack.getD j 0 = backtrack[j] := by simp [h2]
        rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (fits.words j h2)]

/-- The transcription against the pivot, on a state that fits. -/
theorem pivot_link (c : WG.ReplayCounter) (nonce : BitVec 64) (fits : Fits c) :
    (mirrorResult c.counter c.backtrack nonce.toNat).1 = (validate (ofCounter c) nonce).accepted ∧
    (mirrorResult c.counter c.backtrack nonce.toNat).2 = toCounter (validate (ofCounter c) nonce).window ∧
    exitPC c nonce.toNat = (validate (ofCounter c) nonce).exit := by
  have hR : WG.REJECT_AFTER_MESSAGES = 18446744073709543486 := by decide
  have hW : WG.COUNTER_WINDOW_SIZE = 8128 := by decide
  have hwords : WG.COUNTER_BITS_TOTAL / 64 = 128 := by decide
  have hbits : BITS_PER_LONG = 64 := rfl
  have hc := fits.counter
  have good : Good c.backtrack := ⟨fits.size, fits.words⟩
  have same := toCounter_ofCounter c fits
  have tc : (BitVec.ofNat 64 c.counter).toNat = c.counter := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
  have hth := nonce.isLt
  have wc : (ofCounter c).counter = BitVec.ofNat 64 c.counter := rfl
  by_cases h1 : c.counter ≥ WG.REJECT_AFTER_MESSAGES + 1
  · have b1 : limit < BitVec.ofNat 64 c.counter := by unfold limit; bv_omega
    simp only [validate, mirrorResult, mirrorCore, exitPC, wc, b1, h1, true_or, ↓reduceIte, same,
      and_self]
  have b1 : ¬limit < BitVec.ofNat 64 c.counter := by unfold limit; bv_omega
  by_cases h2 : nonce.toNat ≥ WG.REJECT_AFTER_MESSAGES
  · have b2 : limit ≤ nonce := by unfold limit; bv_omega
    simp only [validate, mirrorResult, mirrorCore, exitPC, wc, b1, b2, h1, h2, or_true, ↓reduceIte,
      same, and_self]
  have b2 : ¬limit ≤ nonce := by unfold limit; bv_omega
  have t1 : (nonce + 1).toNat = nonce.toNat + 1 := by bv_omega
  by_cases h3 : WG.COUNTER_WINDOW_SIZE + (nonce.toNat + 1) < c.counter
  · have b3 : nonce + 0x1fc1 < BitVec.ofNat 64 c.counter := by bv_omega
    simp only [validate, mirrorResult, mirrorCore, exitPC, wc, b1, b2, b3, h1, h2, h3, or_self,
      ↓reduceIte, same, and_self]
  have b3 : ¬nonce + 0x1fc1 < BitVec.ofNat 64 c.counter := by bv_omega
  have ti : (((nonce + 1) >>> 6) &&& 127).toNat = (nonce.toNat + 1) / 64 % 128 := by
    rw [BitVec.toNat_and, show BitVec.toNat (127 : BitVec 64) = 127 from rfl,
      Nat.and_two_pow_sub_one_eq_mod _ 7, BitVec.toNat_ushiftRight, t1, Nat.shiftRight_eq_div_pow]
  have tb : ((nonce + 1) &&& 63).toNat = (nonce.toNat + 1) % 64 := by
    rw [BitVec.toNat_and, show BitVec.toNat (63 : BitVec 64) = 63 from rfl,
      Nat.and_two_pow_sub_one_eq_mod _ 6, t1]
  have li : (nonce.toNat + 1) / 64 % 128 < 128 := Nat.mod_lt _ (by omega)
  have lb : (nonce.toNat + 1) % 64 < 64 := Nat.mod_lt _ (by omega)
  by_cases h4 : nonce.toNat + 1 > c.counter
  · have b4 : BitVec.ofNat 64 c.counter < nonce + 1 := by bv_omega
    have cur' : cur (ofCounter c) = BitVec.ofNat 64 (c.counter / 64) := by
      apply BitVec.eq_of_toNat_eq
      show (BitVec.ofNat 64 c.counter >>> 6).toNat = _
      rw [BitVec.toNat_ushiftRight, tc, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
      omega
    have top' : top (ofCounter c) (nonce + 1) = min ((nonce.toNat + 1) / 64 - c.counter / 64) 128 := by
      unfold top
      rw [cur']
      have a : ((nonce + 1) >>> 6).toNat = (nonce.toNat + 1) / 64 := by
        rw [BitVec.toNat_ushiftRight, t1, Nat.shiftRight_eq_div_pow]
      have b : (BitVec.ofNat 64 (c.counter / 64)).toNat = c.counter / 64 := by
        rw [BitVec.toNat_ofNat]; omega
      congr 1
      rw [BitVec.toNat_sub, a, b]
      omega
    obtain ⟨g, vals⟩ := clear_link c.backtrack good (c.counter / 64)
      (min ((nonce.toNat + 1) / 64 - c.counter / 64) 128)
    have T := tested_link (advance (ofCounter c) (nonce + 1)) _ (nonce + 1) _ _ g
      (by intro j; show clearWords _ _ _ j = _; rw [cur', top']; exact vals j) ti tb li lb
    simp only [validate, mirrorResult, mirrorCore, exitPC, wc, b1, b2, b3, b4, h1, h2, h3, h4, or_self,
      ↓reduceIte, hwords, hbits]
    exact ⟨T.1, by rw [← T.2]; show _ = WG.ReplayCounter.mk (nonce + 1).toNat _; rw [t1], rfl⟩
  · have b4 : ¬BitVec.ofNat 64 c.counter < nonce + 1 := by bv_omega
    have T := tested_link (ofCounter c) c.backtrack (nonce + 1) _ _ good (fun j => rfl) ti tb li lb
    simp only [validate, mirrorResult, mirrorCore, exitPC, wc, b1, b2, b3, b4, h1, h2, h3, h4, or_self,
      ↓reduceIte, hwords, hbits]
    exact ⟨T.1, by rw [← T.2]; show _ = WG.ReplayCounter.mk (BitVec.ofNat 64 c.counter).toNat _; rw [tc], rfl⟩

/-! ## The interface theorem -/

theorem windowOf_holds {world : WGWorld} {id : WG.KeypairId} {c : WG.ReplayCounter}
    (held : windowOf world id = some c) :
    ∃ d k, world.dev = some d ∧ d.keypairs.get? id = some k ∧ k.receivingCounter = c := by
  unfold windowOf at held
  cases hd : world.dev with
  | none => rw [hd] at held; cases held
  | some d =>
    rw [hd] at held
    cases hk : d.keypairs.get? id with
    | none =>
      have : (some d).bind (fun d => d.keypairs.get? id) = none := hk
      rw [this] at held; cases held
    | some k =>
      have : (some d).bind (fun d => d.keypairs.get? id) = some k := hk
      rw [this] at held
      exact ⟨d, k, rfl, hk, Option.some.inj held⟩

theorem windowOf_withKeypair (world : WGWorld) (d : WG.Device) (id : WG.KeypairId) (k : WG.Keypair)
    (hd : world.dev = some d) : windowOf (withKeypair world id k) id = some k.receivingCounter := by
  simp [windowOf, withKeypair, hd]

end Binary.C2.Mirror

namespace Binary.C2
open Binary TrustBase Leanux

/-- THE MIRROR LINK (`MirrorFollowsSpec`): a successful run of the mirror's
`counterValidate` on a world holding a fitting replay state returns and leaves what the
pivot `validate` does, and the statement's `exitPC` is the pivot's exit. -/
theorem mirror_follows_spec : MirrorFollowsSpec := by
  intro world world' ambient ambient' id c nonce result fits held run
  obtain ⟨d, k, hd, hk, rfl⟩ := Mirror.windowOf_holds held
  obtain ⟨amb, ran⟩ := Mirror.counterValidate_mirror world d id k nonce.toNat hd hk fits.size ambient
  rw [run] at ran
  have same := Except.ok.inj ran
  have hres : result = _ := congrArg (fun p => p.1.1) same
  have hworld : world' = _ := congrArg (fun p => p.1.2) same
  obtain ⟨accepted, window, exit⟩ := Mirror.pivot_link k.receivingCounter nonce fits
  refine ⟨hres.trans accepted, ?_, exit⟩
  rw [hworld, ← window]
  cases core : Mirror.mirrorCore k.receivingCounter.counter k.receivingCounter.backtrack nonce.toNat with
  | none =>
    have e : (Mirror.mirrorResult k.receivingCounter.counter k.receivingCounter.backtrack nonce.toNat).2 =
        k.receivingCounter := by
      unfold Mirror.mirrorResult; rw [core]
    rw [e]; exact held
  | some r => exact Mirror.windowOf_withKeypair world d id _ hd

#print axioms Binary.C2.mirror_follows_spec

end Binary.C2

/-! ## The world

A world that holds a given replay state: a device whose keypair store has one keypair,
number 0, with that state. -/
namespace Binary.C2
open Binary TrustBase Leanux
local instance : Labels := Binary.Image.linkedLabels

/-- The world with one keypair, number 0, holding `c`. -/
def worldOf (c : WG.ReplayCounter) : WGWorld :=
  { dev := some
      { ifindex := 3, ifname := "wg0"
        keypairs := (∅ : Std.TreeMap WG.KeypairId WG.Keypair).insert 0
          { peer := none, receivingCounter := c } } }

theorem windowOf_worldOf (c : WG.ReplayCounter) : windowOf (worldOf c) 0 = some c := by
  simp [windowOf, worldOf]

/-- An ambient state to run the mirror in: the environment oracle always succeeds and
nothing has been recorded. `counterValidate` never asks the oracle. -/
def ambientStart : Ambient :=
  { env := fun _ _ => true, timing := { advanceWait := 0, traceBound := 0 } }

theorem world_holds : WorldHolds :=
  fun c => ⟨worldOf c, 0, ambientStart, windowOf_worldOf c⟩

#print axioms world_holds
end Binary.C2

/-! ## The witness: tools

A memory built from a list of byte regions, read back by one lemma; address ranges as
lists of numbers, with disjointness decided. -/
namespace Binary.C2.Witness
open Binary TrustBase Leanux Binary.C2 Binary.MemoryBytes
local instance : Labels := Binary.Image.linkedLabels

/-- The memory holding each region's bytes at its base address. -/
def build : List (Nat × List UInt8) → Mem 64
  | [] => ∅
  | (base, bytes) :: rest => (build rest).storeBytes (.ofNat 64 base) bytes

/-- Every region ends within the address space and no two regions overlap. -/
def wellPlaced : List (Nat × List UInt8) → Bool
  | [] => true
  | r :: rest =>
    decide (r.1 + r.2.length ≤ 18446744073709551616) &&
    rest.all (fun q => decide (r.1 + r.2.length ≤ q.1 ∨ q.1 + q.2.length ≤ r.1)) &&
    wellPlaced rest

theorem wellPlaced_bound : ∀ (regions : List (Nat × List UInt8)), wellPlaced regions = true →
    ∀ q ∈ regions, q.1 + q.2.length ≤ 18446744073709551616
  | [], _, q, inside => by cases inside
  | r :: rest, placed, q, inside => by
    simp only [wellPlaced, Bool.and_eq_true, decide_eq_true_eq] at placed
    rcases List.mem_cons.mp inside with rfl | later
    · exact placed.1.1
    · exact wellPlaced_bound rest placed.2 q later

/-- A byte of a region is read back. -/
theorem build_get : ∀ (regions : List (Nat × List UInt8)), wellPlaced regions = true →
    ∀ (base : Nat) (bytes : List UInt8), (base, bytes) ∈ regions →
    ∀ (offset : Nat) (bound : offset < bytes.length),
      (build regions).get? (.ofNat 64 (base + offset)) = some bytes[offset]
  | [], _, _, _, inside, _, _ => by cases inside
  | (first, content) :: rest, placed, base, bytes, inside, offset, bound => by
    have bounds := wellPlaced_bound _ placed
    simp only [wellPlaced, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at placed
    rcases List.mem_cons.mp inside with same | later
    · cases same
      rw [BitVec.ofNat_add]
      exact get_storeBytes _ _ _ (by have := placed.1.1; omega) offset bound
    · have earlier := build_get rest placed.2 base bytes later offset bound
      have apart := placed.1.2 (base, bytes) later
      have fits := bounds (base, bytes) (List.mem_cons_of_mem _ later)
      have ends := placed.1.1
      rw [← earlier]
      have absent : BitVec.ofNat 64 (base + offset) ∉ content.At (BitVec.ofNat 64 first) := by
        intro present
        rw [mem_At_iff] at present
        obtain ⟨i, hi, equal⟩ := present
        have numbers := congrArg BitVec.toNat equal
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at numbers
        dsimp only at apart fits
        omega
      have missing := Std.ExtHashMap.getElem?_eq_none absent
      simp only [build, Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?,
        Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union, missing, Option.none_or]

/-- A load inside a region gives the region's bytes. -/
theorem build_load (regions : List (Nat × List UInt8)) (placed : wellPlaced regions = true)
    (base : Nat) (bytes : List UInt8) (inside : (base, bytes) ∈ regions)
    (offset width : Nat) (bound : offset + width ≤ bytes.length) :
    (build regions).loadInt (.ofNat 64 (base + offset)) width =
      some (Int.ofBytes ((bytes.drop offset).take width)) := by
  have read : (build regions).loadBytes (.ofNat 64 (base + offset)) width =
      some ((bytes.drop offset).take width) := by
    rw [loadBytes_iff]
    refine ⟨by simp only [List.length_take, List.length_drop]; omega, ?_⟩
    intro i hi
    have hi' : i < width ∧ offset + i < bytes.length := by
      simp only [List.length_take, List.length_drop] at hi; omega
    rw [← BitVec.ofNat_add, Nat.add_assoc,
      build_get regions placed base bytes inside (offset + i) hi'.2]
    simp
  simp only [Mem.loadInt, read, Option.map_some]

theorem ofBytes_zeros : ∀ n : Nat, Int.ofBytes (List.replicate n 0) = 0
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, Int.ofBytes_cons, ofBytes_zeros n]; rfl

/-- A load inside a region of zero bytes gives zero. -/
theorem build_load_zero (regions : List (Nat × List UInt8)) (placed : wellPlaced regions = true)
    (base size : Nat) (inside : (base, List.replicate size 0) ∈ regions)
    (offset width : Nat) (bound : offset + width ≤ size) :
    (build regions).loadInt (.ofNat 64 (base + offset)) width = some 0 := by
  rw [build_load regions placed base _ inside offset width (by simpa using bound),
    List.drop_replicate, List.take_replicate, ofBytes_zeros]

/-- A byte inside a region is mapped. -/
theorem build_mapped (regions : List (Nat × List UInt8)) (placed : wellPlaced regions = true)
    (base : Nat) (bytes : List UInt8) (inside : (base, bytes) ∈ regions)
    (offset : Nat) (bound : offset < bytes.length) :
    ((build regions).get? (.ofNat 64 (base + offset))).isSome = true := by
  rw [build_get regions placed base bytes inside offset bound]; rfl

/-- `a` lies in one of the ranges, each given as its base and length. -/
def Covers (ranges : List (Nat × Nat)) (a : BitVec 64) : Prop :=
  ∃ r ∈ ranges, InRange (.ofNat 64 r.1) r.2 a

/-- No range of the first list meets a range of the second. -/
def apart (xs ys : List (Nat × Nat)) : Bool :=
  xs.all fun x => ys.all fun y =>
    decide (x.1 + x.2 ≤ 18446744073709551616 ∧ y.1 + y.2 ≤ 18446744073709551616 ∧
      (x.1 + x.2 ≤ y.1 ∨ y.1 + y.2 ≤ x.1))

theorem covers_apart (xs ys : List (Nat × Nat)) (separate : apart xs ys = true) (a : BitVec 64) :
    Covers xs a → ¬Covers ys a := by
  rintro ⟨x, hx, i, hi, rfl⟩ ⟨y, hy, j, hj, equal⟩
  have fact := List.all_eq_true.mp (List.all_eq_true.mp separate x hx) y hy
  simp only [decide_eq_true_eq] at fact
  have numbers := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at numbers
  omega

theorem Covers.left {xs : List (Nat × Nat)} (ys : List (Nat × Nat)) {a : BitVec 64} :
    Covers xs a → Covers (xs ++ ys) a :=
  fun ⟨r, inside, holds⟩ => ⟨r, List.mem_append_left _ inside, holds⟩

theorem Covers.right (xs : List (Nat × Nat)) {ys : List (Nat × Nat)} {a : BitVec 64} :
    Covers ys a → Covers (xs ++ ys) a :=
  fun ⟨r, inside, holds⟩ => ⟨r, List.mem_append_right _ inside, holds⟩

end Binary.C2.Witness

/-! ## The witness: the decoder -/
namespace Binary.C2.Witness
open Binary TrustBase Leanux Binary.C2 Binary.MemoryBytes
local instance : Labels := Binary.Image.linkedLabels

/-- The decoder: the range's literal terms (the two 8-byte callback entries among them),
or else the landed service image. -/
def fetch (pc : Int64) : Option Decoded :=
  (Range.fetch pc).orElse fun _ => ServiceImage.fetch pc

/-- The addresses of a run of sized directives. -/
def starts : Int64 → List (Kraken.Sized Directive) → List Int64
  | _, [] => []
  | pc, ⟨_, n⟩ :: rest => pc :: starts (pc + .ofNat n) rest

theorem fetchIn_starts : ∀ (code : List (Kraken.Sized Directive)) (pc target : Int64)
    (i : Decoded), Image.fetchIn pc code target = some i → target ∈ starts pc code
  | [], _, _, _, fetched => by simp [Image.fetchIn] at fetched
  | ⟨d, n⟩ :: rest, pc, target, i, fetched => by
    unfold Image.fetchIn at fetched
    split at fetched
    · next here => exact here ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (fetchIn_starts rest _ target i fetched)

/-- Every address the range's terms decode. -/
def rangeStarts : List Int64 :=
  starts Range.entry Range.code ++ (starts Range.cmp8Entry Range.cmp8Stub ++
    starts Range.constCmp8Entry Range.constCmp8Stub)

theorem range_starts (pc : Int64) (i : Decoded) (fetched : Range.fetch pc = some i) :
    pc ∈ rangeStarts := by
  unfold Range.fetch at fetched
  unfold rangeStarts
  cases first : Image.fetchIn Range.entry Range.code pc with
  | some j => exact List.mem_append_left _ (fetchIn_starts _ _ _ j first)
  | none =>
    rw [first] at fetched
    apply List.mem_append_right
    cases second : Image.fetchIn Range.cmp8Entry Range.cmp8Stub pc with
    | some j => exact List.mem_append_left _ (fetchIn_starts _ _ _ j second)
    | none =>
      rw [second] at fetched
      exact List.mem_append_right _ (fetchIn_starts _ _ _ i fetched)

theorem service_row (pc : Int64) (i : Decoded) (fetched : ServiceImage.fetch pc = some i) :
    ∃ row ∈ ServiceImage.decoded, (row.1 == pc.toUInt64.toNat) = true := by
  unfold ServiceImage.fetch at fetched
  cases found : ServiceImage.decoded.find? (fun row => row.1 == pc.toUInt64.toNat) with
  | none => rw [found] at fetched; cases fetched
  | some row => exact ⟨row, List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩

/-- The range's terms and the service image decode disjoint sets of addresses. -/
theorem images_apart : ∀ t ∈ rangeStarts, ∀ row ∈ ServiceImage.decoded,
    (row.1 == t.toUInt64.toNat) = false := by
  decide +kernel

theorem reading : Reading fetch := by
  refine ⟨?_, ?_⟩
  · intro pc i fetched
    simp only [fetch, fetched, Option.orElse_some]
  · intro pc i fetched
    cases ranged : Range.fetch pc with
    | none => simp only [fetch, ranged, Option.orElse_none, fetched]
    | some j =>
      obtain ⟨row, inside, same⟩ := service_row pc i fetched
      rw [images_apart pc (range_starts pc j ranged) row inside] at same
      cases same

#print axioms reading
end Binary.C2.Witness

/-! ## The witness: the entry state

Coverage is in PC mode (`kcov_mode` 2) with an empty 64-word buffer, in softirq context
(preempt count 0x100) with softirq coverage enabled: the state in which the callbacks
record. The replay state is the fresh one: counter 0, bitmap clear. The packet counter
is 5. Addresses are those of the statement's executed tests. -/
namespace Binary.C2.Witness
open Binary TrustBase Leanux Binary.C2 Binary.MemoryBytes
local instance : Labels := Binary.Image.linkedLabels

/-- The mapped regions: the stack slots (`sp - 8` to `sp + 0x20`), the packet counter at
`skb + 0x28`, the 1032 window bytes at `kp + 136`, the current-task pointer, the preempt
count, the four coverage fields of the task, the coverage buffer. -/
def regions : List (Nat × List UInt8) :=
  [(0x4007f8, List.replicate 40 0),
   (0x600028, [5, 0, 0, 0, 0, 0, 0, 0]),
   (0x700088, List.replicate 1032 0),
   (0xffffffff81cc85c0, [0, 0, 0x50, 0, 0, 0, 0, 0]),
   (0xffffffff81cc85c8, [0, 1, 0, 0]),
   (0x5006e0, [2, 0, 0, 0]),
   (0x5006e4, [64, 0, 0, 0]),
   (0x5006e8, [0, 0, 0x80, 0, 0, 0, 0, 0]),
   (0x500704, [1, 0, 0, 0]),
   (0x800000, List.replicate 512 0)]

theorem in_stack : (((0x4007f8, List.replicate 40 0) : Nat × List UInt8)) ∈ regions :=
  List.mem_of_getElem? (i := 0) rfl
theorem in_packet : (((0x600028, [5, 0, 0, 0, 0, 0, 0, 0]) : Nat × List UInt8)) ∈ regions :=
  List.mem_of_getElem? (i := 1) rfl
theorem in_window : (((0x700088, List.replicate 1032 0) : Nat × List UInt8)) ∈ regions :=
  List.mem_of_getElem? (i := 2) rfl
theorem in_task : (((0xffffffff81cc85c0, [0, 0, 0x50, 0, 0, 0, 0, 0]) : Nat × List UInt8)) ∈ regions :=
  List.mem_of_getElem? (i := 3) rfl
theorem in_count : (((0xffffffff81cc85c8, [0, 1, 0, 0]) : Nat × List UInt8)) ∈ regions :=
  List.mem_of_getElem? (i := 4) rfl
theorem in_mode : (((0x5006e0, [2, 0, 0, 0]) : Nat × List UInt8)) ∈ regions :=
  List.mem_of_getElem? (i := 5) rfl
theorem in_capacity : (((0x5006e4, [64, 0, 0, 0]) : Nat × List UInt8)) ∈ regions :=
  List.mem_of_getElem? (i := 6) rfl
theorem in_area : (((0x5006e8, [0, 0, 0x80, 0, 0, 0, 0, 0]) : Nat × List UInt8)) ∈ regions :=
  List.mem_of_getElem? (i := 7) rfl
theorem in_softirq : (((0x500704, [1, 0, 0, 0]) : Nat × List UInt8)) ∈ regions :=
  List.mem_of_getElem? (i := 8) rfl
theorem in_buffer : (((0x800000, List.replicate 512 0) : Nat × List UInt8)) ∈ regions :=
  List.mem_of_getElem? (i := 9) rfl

theorem placed : wellPlaced regions = true := by decide +kernel

def memory : Mem 64 := build regions

def state : MachineState :=
  ⟨{ regs := { rsp := 0x400800, r13 := 0x700000, rbx := 0x600000 }, dmem := memory }, Range.entry⟩

def layout : KcovLayout :=
  { task := 0x500000#64, area := 0x800000#64, capacity := 64#32, mode := 2#32,
    softirqEnabled := 1#32 }

def preempt : BitVec 32 := 0x100#32
def kp : BitVec 64 := 0x700000#64
def skb : BitVec 64 := 0x600000#64
def nonce : BitVec 64 := 5#64

/-- The fresh replay state. -/
def fresh : WG.ReplayCounter := { counter := 0, backtrack := Array.replicate 128 0 }

/-! ### Loads -/

theorem load (base : Nat) (bytes : List UInt8) (inside : (base, bytes) ∈ regions)
    (offset width : Nat) (bound : offset + width ≤ bytes.length) :
    memory.loadInt (.ofNat 64 (base + offset)) width =
      some (Int.ofBytes ((bytes.drop offset).take width)) :=
  build_load regions placed base bytes inside offset width bound

theorem nonce_held : state.data.dmem.loadInt (skb + 0x28) 8 = some (nonce.toNat : Int) :=
  load 0x600028 _ in_packet 0 8 (by decide)

theorem fields : Layouts.ReplayFields state.data.dmem (windowBase kp) fresh := by
  refine ⟨?_, by simp only [fresh, Array.size_replicate, Layouts.replayWords], ?_⟩
  · exact build_load_zero regions placed 0x700088 1032 in_window 0 8 (by decide)
  · intro j hj
    have hj' : j < 128 := by simpa only [fresh, Array.size_replicate] using hj
    have read := build_load_zero regions placed 0x700088 1032 in_window (8 + j * 8) 8 (by omega)
    have value : fresh.backtrack[j]'hj = 0 := by simp only [fresh, Array.getElem_replicate]
    rw [value]
    have address : windowBase kp + .ofNat 64 (Layouts.replay_backtrack + j * Layouts.replayWordBytes) =
        .ofNat 64 (0x700088 + (8 + j * 8)) := by
      have base : windowBase kp = .ofNat 64 0x700088 := by decide
      rw [base, ← BitVec.ofNat_add]; rfl
    rw [address]
    exact read

theorem metadata : KcovMetadata layout state.data.dmem := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have read := load 0xffffffff81cc85c0 _ in_task 0 8 (by decide)
    show Option.map (BitVec.ofInt 64) (memory.loadInt _ 8) = _
    exact (congrArg (Option.map (BitVec.ofInt 64)) read).trans (by decide)
  · have read := load 0x5006e0 _ in_mode 0 4 (by decide)
    show Option.map (BitVec.ofInt 32) (memory.loadInt _ 4) = _
    exact (congrArg (Option.map (BitVec.ofInt 32)) read).trans (by decide)
  · have read := load 0x5006e4 _ in_capacity 0 4 (by decide)
    show Option.map (BitVec.ofInt 32) (memory.loadInt _ 4) = _
    exact (congrArg (Option.map (BitVec.ofInt 32)) read).trans (by decide)
  · have read := load 0x5006e8 _ in_area 0 8 (by decide)
    show Option.map (BitVec.ofInt 64) (memory.loadInt _ 8) = _
    exact (congrArg (Option.map (BitVec.ofInt 64)) read).trans (by decide)
  · have read := load 0x500704 _ in_softirq 0 4 (by decide)
    show Option.map (BitVec.ofInt 32) (memory.loadInt _ 4) = _
    exact (congrArg (Option.map (BitVec.ofInt 32)) read).trans (by decide)

theorem count_held : load32 state.data.dmem preemptCountAddress = some preempt := by
  have read := load 0xffffffff81cc85c8 _ in_count 0 4 (by decide)
  show Option.map (BitVec.ofInt 32) (memory.loadInt _ 4) = _
  exact (congrArg (Option.map (BitVec.ofInt 32)) read).trans (by decide)

theorem buffer : KcovBuffer layout state.data.dmem := by
  refine ⟨?_, 0, Nat.zero_le _, ?_⟩
  · intro word hw
    have hw' : word < 64 := hw
    have read := build_load_zero regions placed 0x800000 512 in_buffer (8 * word) 8 (by omega)
    have address : layout.area + .ofNat 64 (8 * word) = .ofNat 64 (0x800000 + 8 * word) := by
      rw [BitVec.ofNat_add]; rfl
    rw [address]
    exact (congrArg Option.isSome read).trans rfl
  · have read := build_load_zero regions placed 0x800000 512 in_buffer 0 8 (by decide)
    show Option.map (BitVec.ofInt 64) (memory.loadInt _ 8) = _
    exact (congrArg (Option.map (BitVec.ofInt 64)) read).trans (by decide)

theorem coverage : KcovState layout preempt state.data.dmem :=
  ⟨metadata, count_held, fun _ => buffer⟩

end Binary.C2.Witness

/-! ## The witness: separations, the two mirror runs, revisitability -/
namespace Binary.C2.Witness
open Binary TrustBase Leanux Binary.C2 Binary.MemoryBytes
local instance : Labels := Binary.Image.linkedLabels

/-! ### Address ranges -/

def stackRanges : List (Nat × Nat) := [(0x4007f8, 8), (0x400810, 16)]
def windowRanges : List (Nat × Nat) := [(0x700088, 1032)]
def countRanges : List (Nat × Nat) := [(0xffffffff81cc85c8, 4)]
def metadataRanges : List (Nat × Nat) :=
  [(0xffffffff81cc85c0, 8), (0x5006e0, 4), (0x5006e4, 4), (0x5006e8, 8), (0x500704, 4)]
def storageRanges : List (Nat × Nat) := [(0x800000, 8), (0x800000, 512)]
def packetRanges : List (Nat × Nat) := [(0x600028, 8)]

theorem stack_covers (a : BitVec 64) :
    stackBytes state.data.regs.rsp.toBitVec a → Covers stackRanges a := by
  rintro (h | h)
  · exact ⟨(0x4007f8, 8), List.mem_cons_self, h⟩
  · exact ⟨(0x400810, 16), List.mem_cons_of_mem _ List.mem_cons_self, h⟩

theorem window_covers (a : BitVec 64) : windowBytes kp a → Covers windowRanges a :=
  fun h => ⟨(0x700088, 1032), List.mem_cons_self, h⟩

theorem count_covers (a : BitVec 64) : InRange preemptCountAddress 4 a → Covers countRanges a :=
  fun h => ⟨(0xffffffff81cc85c8, 4), List.mem_cons_self, h⟩

theorem footprint_covers (a : BitVec 64) :
    Footprint state.data.regs.rsp.toBitVec kp a →
      Covers (stackRanges ++ (windowRanges ++ countRanges)) a := by
  rintro (h | h | h)
  · exact (stack_covers a h).left _
  · exact Covers.right _ ((window_covers a h).left _)
  · exact Covers.right _ (Covers.right _ (count_covers a h))

theorem metadata_covers (a : BitVec 64) : KcovMetadataBytes layout a → Covers metadataRanges a := by
  rintro (h | h | h | h | h)
  · exact ⟨(0xffffffff81cc85c0, 8), List.mem_of_getElem? (i := 0) rfl, h⟩
  · exact ⟨(0x5006e0, 4), List.mem_of_getElem? (i := 1) rfl, h⟩
  · exact ⟨(0x5006e4, 4), List.mem_of_getElem? (i := 2) rfl, h⟩
  · exact ⟨(0x5006e8, 8), List.mem_of_getElem? (i := 3) rfl, h⟩
  · exact ⟨(0x500704, 4), List.mem_of_getElem? (i := 4) rfl, h⟩

theorem storage_covers (a : BitVec 64) : KcovStorageBytes layout a → Covers storageRanges a := by
  rintro (h | h)
  · exact ⟨(0x800000, 8), List.mem_of_getElem? (i := 0) rfl, h⟩
  · exact ⟨(0x800000, 512), List.mem_of_getElem? (i := 1) rfl, h⟩

theorem coverage_covers (a : BitVec 64) :
    coverageBytes layout a → Covers (metadataRanges ++ storageRanges) a := by
  rintro (h | ⟨_, h⟩)
  · exact (metadata_covers a h).left _
  · exact Covers.right _ (storage_covers a h)

/-! ### `Context` -/

theorem stack_mapped (a : BitVec 64) (inside : stackBytes state.data.regs.rsp.toBitVec a) :
    (state.data.dmem.get? a).isSome = true := by
  have low : state.data.regs.rsp.toBitVec - 8 = .ofNat 64 0x4007f8 := by decide
  have high : state.data.regs.rsp.toBitVec + 0x10 = .ofNat 64 0x400810 := by decide
  rcases inside with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · rw [low, ← BitVec.ofNat_add]
    exact build_mapped regions placed 0x4007f8 _ in_stack i (by rw [List.length_replicate]; omega)
  · rw [high, ← BitVec.ofNat_add, show 0x400810 + i = 0x4007f8 + (24 + i) by omega]
    exact build_mapped regions placed 0x4007f8 _ in_stack (24 + i)
      (by rw [List.length_replicate]; omega)

theorem context : Context layout preempt state kp skb nonce where
  pc := rfl
  keypair := by decide
  packet := by decide
  nonce := nonce_held
  window := fields_mapped _ kp fresh fields
  aligned := by decide
  stack := stack_mapped
  coverage := coverage
  stackWindow := fun a h w =>
    covers_apart stackRanges windowRanges (by decide) a (stack_covers a h) (window_covers a w)
  stackPreempt := fun a h c =>
    covers_apart stackRanges countRanges (by decide) a (stack_covers a h) (count_covers a c)
  windowPreempt := fun a w c =>
    covers_apart windowRanges countRanges (by decide) a (window_covers a w) (count_covers a c)
  coverageApart := fun a c f =>
    covers_apart (metadataRanges ++ storageRanges) (stackRanges ++ (windowRanges ++ countRanges))
      (by decide) a (coverage_covers a c) (footprint_covers a f)
  coverageMetadata := fun a _ s m =>
    covers_apart storageRanges metadataRanges (by decide) a (storage_covers a s) (metadata_covers a m)

/-! ### Revisitability -/

/-- The packet's counter slot is outside everything the range and the callbacks write. -/
theorem packet_outside (i : Nat) (hi : i < 8) :
    ¬(Footprint state.data.regs.rsp.toBitVec kp (skb + 0x28 + .ofNat 64 i) ∨
      ((layout.mode = 2 ∨ layout.mode = 3) ∧ KcovStorageBytes layout (skb + 0x28 + .ofNat 64 i))) := by
  have here : Covers packetRanges (skb + 0x28 + .ofNat 64 i) :=
    ⟨(0x600028, 8), List.mem_cons_self, i, hi, rfl⟩
  rintro (f | ⟨_, s⟩)
  · exact covers_apart packetRanges (stackRanges ++ (windowRanges ++ countRanges)) (by decide) _
      here (footprint_covers _ f)
  · exact covers_apart packetRanges storageRanges (by decide) _ here (storage_covers _ s)

theorem revisit (t : MachineState) (kept : Kept layout preempt kp state t)
    (stack : ∀ a, stackBytes state.data.regs.rsp.toBitVec a → (t.data.dmem.get? a).isSome = true)
    (window : ∀ a, windowBytes kp a → (t.data.dmem.get? a).isSome = true) :
    Context layout (preempt + 0x200) ⟨t.data, Range.entry⟩ kp skb nonce where
  pc := rfl
  keypair := by
    show t.data.regs.r13.toBitVec = kp
    rw [kept.r13]; exact context.keypair
  packet := by
    show t.data.regs.rbx.toBitVec = skb
    rw [kept.rbx]; exact context.packet
  nonce := by
    show t.data.dmem.loadInt (skb + 0x28) 8 = _
    rw [← kept.frame.loadInt (skb + 0x28) 8 packet_outside]
    exact nonce_held
  window := window
  aligned := by
    show t.data.regs.rsp.toNat % 8 = 0
    rw [kept.rsp]; exact context.aligned
  stack := by
    show ∀ a, stackBytes t.data.regs.rsp.toBitVec a → _
    rw [kept.rsp]; exact stack
  coverage := kept.coverage
  stackWindow := by
    show ∀ a, stackBytes t.data.regs.rsp.toBitVec a → _
    rw [kept.rsp]; exact context.stackWindow
  stackPreempt := by
    show ∀ a, stackBytes t.data.regs.rsp.toBitVec a → _
    rw [kept.rsp]; exact context.stackPreempt
  windowPreempt := context.windowPreempt
  coverageApart := by
    show ∀ a, coverageBytes layout a → ¬Footprint t.data.regs.rsp.toBitVec kp a
    rw [kept.rsp]; exact context.coverageApart
  coverageMetadata := context.coverageMetadata

/-! ### The mirror, twice -/

/-- The mirror's `counterValidate` runs to completion on a world holding a fitting state,
and returns and leaves what the pivot does. -/
theorem mirror_runs (world : WGWorld) (id : WG.KeypairId) (c : WG.ReplayCounter)
    (nonce : BitVec 64) (ambient : Ambient) (fits : Fits c) (held : windowOf world id = some c) :
    ∃ world' ambient',
      ((WG.counterValidate id nonce.toNat).run world).run ambient =
        .ok (((validate (ofCounter c) nonce).accepted, world'), ambient') ∧
      windowOf world' id = some (toCounter (validate (ofCounter c) nonce).window) := by
  obtain ⟨d, k, hd, hk, rfl⟩ := Mirror.windowOf_holds held
  obtain ⟨ambient', ran⟩ :=
    Mirror.counterValidate_mirror world d id k nonce.toNat hd hk fits.size ambient
  have spec := mirror_follows_spec world _ ambient ambient' id _ nonce _ fits held ran
  exact ⟨_, ambient', by rw [← spec.1]; exact ran, spec.2.1⟩

theorem fits_toCounter (w : Window) : Fits (toCounter w) where
  counter := w.counter.isLt
  size := by simp only [toCounter, Array.size_ofFn]
  words := by
    intro i h
    simp only [toCounter, Array.getElem_ofFn]
    exact (w.words i).isLt

/-- The pivot accepts counter 5 on the fresh window. -/
theorem first_accepts : (validate (ofCounter fresh) nonce).accepted = true := by decide +kernel

/-- The window the first visit leaves. -/
def after : WG.ReplayCounter := toCounter (validate (ofCounter fresh) nonce).window

/-- The pivot refuses counter 5 on the window the first visit leaves. -/
theorem second_refuses : (validate (ofCounter after) nonce).accepted = false := by decide +kernel

end Binary.C2.Witness

namespace Binary.C2
open Binary TrustBase Leanux
local instance : Labels := Binary.Image.linkedLabels

theorem witness_start : WitnessStart := by
  have fits : Fits Witness.fresh := fields_fit _ _ _ Witness.fields
  obtain ⟨world₁, ambient₁, first, held₁⟩ :=
    Witness.mirror_runs (worldOf Witness.fresh) 0 Witness.fresh Witness.nonce ambientStart fits
      (windowOf_worldOf _)
  obtain ⟨world₂, ambient₂, second, _⟩ :=
    Witness.mirror_runs world₁ 0 Witness.after Witness.nonce ambient₁ (Witness.fits_toCounter _) held₁
  rw [Witness.first_accepts] at first
  rw [Witness.second_refuses] at second
  exact ⟨Witness.fetch, Witness.layout, Witness.preempt, Witness.state, Witness.kp, Witness.skb,
    Witness.nonce, worldOf Witness.fresh, world₁, world₂, ambientStart, ambient₁, ambient₂, 0,
    Witness.fresh, Witness.reading, Witness.context, Witness.fields, windowOf_worldOf _, first,
    second, Witness.revisit⟩

#print axioms witness_start
end Binary.C2

/-! ## What the package delivers -/
namespace Binary.C2
open Binary TrustBase Leanux
local instance : Labels := Binary.Image.linkedLabels

/-- The ten propositions of the package that the assembly takes together; the eleventh,
`WitnessStart`, is `witness_start`. -/
theorem representation : Representation where
  mapped := window_mapped
  ofFields := window_of_fields
  toFields := fields_of_window
  fit := fields_fit
  retained := fields_retained
  fieldsMapped := fields_mapped
  mirror := mirror_follows_spec
  world := world_holds
  determined := first_exit_determined
  exists_ := first_exit_exists

#print axioms representation
end Binary.C2
