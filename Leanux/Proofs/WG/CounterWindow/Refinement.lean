import Leanux.Proofs.WG.CounterWindow.Model

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.CounterWindow
open Leanux Leanux.WG

@[simp] theorem except_pure {α : Type} (a : α) :
    (pure a : Except Stop α) = .ok a := rfl

@[simp] theorem except_ok_bind {α β : Type} (a : α) (f : α → Except Stop β) :
    (Except.ok a >>= f) = f a := rfl

/-- The mirror's branch recorder, presented as a pure World update. -/
def record (w : World) (d : Decision) (outcome : Bool) : World :=
  { w with steps := w.steps.push { decision := d, outcome, netRx := w.netRxSection } }

@[simp] theorem branch_run (w : World) (d : Decision) (outcome : Bool) :
    (branch d outcome).run w = .ok (outcome, record w d outcome) := rfl

/-- A comparison record retains the mirror's two concrete operands. -/
def recordCmp (w : World) (d : Decision) (outcome : Bool) (a b : Int) : World :=
  {w with steps := w.steps.push {decision := d, outcome, operands := some (a,b), netRx := w.netRxSection}}

@[simp] theorem branchCmp_run (w : World) (d : Decision) (outcome : Bool) (a b : Int) :
    (branchCmp d outcome a b).run w = .ok (outcome, recordCmp w d outcome a b) := rfl

/-- The actual body of the mirror's word-clearing loop. -/
def clearBody (current : Nat) (i : Nat) (a : Array Nat) : M (ForInStep (Array Nat)) := do
  _ ← branch .ctrClearIter true
  let j := (i + current) % 128
  if j ≥ a.size then
    let _ : Unit ← invariant s!"backtrack[{j}] beyond the bitmap"
    return .yield (a.set! j 0)
  else return .yield (a.set! j 0)

/-- All bookkeeping effects of the loop, separated from its bitmap effect. -/
def clearRecords : World → List Nat → World
  | w, [] => w
  | w, _ :: xs => clearRecords (record w .ctrClearIter true) xs

@[simp] theorem clearRecords_k (w : World) (xs : List Nat) :
    (clearRecords w xs).k = w.k := by
  induction xs generalizing w with
  | nil => rfl
  | cons i xs ih => simpa [clearRecords, record] using ih (record w .ctrClearIter true)

/-- The mirror's monadic clear loop performs exactly the pure list of clears.
It cannot stop when the replay bitmap has the C shape. -/
theorem clear_loop_run (a : Array Nat) (current : Nat) (xs : List Nat)
    (w : World) (hsize : a.size = 128) :
    (forIn xs a (clearBody current)).run w =
      .ok (clear a current xs, clearRecords w xs) := by
  induction xs generalizing a w with
  | nil => rfl
  | cons i xs ih =>
    have hj : ¬(i + current) % 128 ≥ a.size := by rw [hsize]; omega
    simp only [List.forIn_cons, clearBody, hj, if_false, bind_pure_comp,
      StateT.run_bind]
    change (forIn xs (a.set! ((i + current) % 128) 0) (clearBody current)).run
      (record w .ctrClearIter true) = _
    exact ih _ _ (by simp [hsize])

@[simp] theorem getKeypair_run (w : World) (d : Device) (kp : KeypairId) (k : Keypair)
    (hd : w.k.wg = some d) (hk : d.keypairs.get? kp = some k) :
    (getKeypair kp).run w = .ok (k, w) := by
  change d.keypairs[kp]? = some k at hk
  simp [getKeypair, getDev, getK, hd, hk]

def store (w : World) (kp : KeypairId) (k : Keypair) : World :=
  { w with k := { w.k with wg := w.k.wg.map fun d =>
    { d with keypairs := d.keypairs.insert kp k } } }

@[simp] theorem setKeypair_run (w : World) (kp : KeypairId) (k : Keypair) :
    (setKeypair kp k).run w = .ok ((), store w kp k) := rfl

/-- A direct operational transcription of receive.c after its keypair lookup.
The result includes the mirror's bookkeeping, to make the refinement exact. -/
def cExecution (kp : KeypairId) (nonce : Nat) (k : Keypair) (w : World) : Bool × World :=
  let c := k.receivingCounter
  let w := recordCmp w .ctrRejectCounter (c.counter ≥ REJECT_AFTER_MESSAGES + 1) c.counter (REJECT_AFTER_MESSAGES + 1)
  if c.counter ≥ REJECT_AFTER_MESSAGES + 1 then (false, w) else
  let w := recordCmp w .ctrRejectTheirs (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES
  if nonce ≥ REJECT_AFTER_MESSAGES then (false, w) else
  let n := nonce + 1
  let w := record w .ctrTooOld (8128 + n < c.counter)
  if 8128 + n < c.counter then (false, w) else
  let w := record w .ctrAdvance (n > c.counter)
  let (a, high, w) := if n > c.counter then
      let xs := List.range' 1 (min (n / 64 - c.counter / 64) 128)
      (clear c.backtrack (c.counter / 64) xs, n,
        record (clearRecords w xs) .ctrClearIter false)
    else (c.backtrack, c.counter, w)
  let word := a[slot n]!
  let c' : ReplayCounter :=
    { counter := high
      backtrack := a.set! (slot n) (word ||| (1 <<< bit n)) }
  let w := store w kp { k with receivingCounter := c' }
  ((word >>> bit n) % 2 == 0, w)

/-- The word-clearing loop in the unchanged mirror is the C loop. -/
theorem mirror_clear_loop (a : Array Nat) (current top : Nat) (w : World)
    (hsize : a.size = 128) :
    (forIn [1:top + 1] a (clearBody current)).run w =
      .ok (clear a current (List.range' 1 top), clearRecords w (List.range' 1 top)) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simpa [Std.Legacy.Range.size] using clear_loop_run a current (List.range' 1 top) w hsize

/-- Exact successful execution equality for the fixed mirror's validator. -/
theorem counterValidate_execution (w : World) (d : Device) (kp : KeypairId)
    (k : Keypair) (nonce : Nat) (hd : w.k.wg = some d)
    (hk : d.keypairs.get? kp = some k) (hsize : k.receivingCounter.backtrack.size = 128) :
    (counterValidate kp nonce).run w = .ok (cExecution kp nonce k w) := by
  by_cases h1 : k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES + 1
  · simp [counterValidate, getKeypair_run w d kp k hd hk, WG.orM, h1, cExecution]
  · by_cases h2 : nonce ≥ REJECT_AFTER_MESSAGES
    · simp [counterValidate, getKeypair_run w d kp k hd hk, WG.orM, h1, h2, cExecution]
    · by_cases h3 : 8128 + (nonce + 1) < k.receivingCounter.counter
      · simp [counterValidate, getKeypair_run w d kp k hd hk, WG.orM, h1, h2, h3,
          cExecution, COUNTER_WINDOW_SIZE]
      · by_cases h4 : nonce + 1 > k.receivingCounter.counter
        · simp only [counterValidate, StateT.run_bind, getKeypair_run w d kp k hd hk,
            except_ok_bind, WG.orM, branch_run, branchCmp_run, h1, h2, h3, h4, decide_false, decide_true,
            Bool.false_eq_true, if_false, if_true, COUNTER_WINDOW_SIZE,
            COUNTER_BITS_TOTAL, BITS_PER_LONG, cExecution]
          simp only [show 8192 / 64 = 128 from rfl]
          have hloop := mirror_clear_loop _ (k.receivingCounter.counter / 64)
            (min ((nonce + 1) / 64 - k.receivingCounter.counter / 64) 128)
            (record (record (recordCmp (recordCmp w .ctrRejectCounter false k.receivingCounter.counter
              (REJECT_AFTER_MESSAGES + 1)) .ctrRejectTheirs false nonce REJECT_AFTER_MESSAGES)
              .ctrTooOld false) .ctrAdvance true) hsize
          unfold clearBody at hloop
          rw [hloop]
          simp only [except_ok_bind]
          rw [Array.getElem?_eq_some_getElem!]
          · rfl
          · simp [hsize, Nat.mod_lt _ (by decide : 0 < 128)]
        · simp only [counterValidate, StateT.run_bind, getKeypair_run w d kp k hd hk,
            except_ok_bind, WG.orM, branch_run, branchCmp_run, h1, h2, h3, h4, decide_false,
            Bool.false_eq_true, if_false, COUNTER_WINDOW_SIZE,
            COUNTER_BITS_TOTAL, BITS_PER_LONG, cExecution]
          simp only [show 8192 / 64 = 128 from rfl]
          rw [Array.getElem?_eq_some_getElem!]
          · rfl
          · simp [hsize, Nat.mod_lt _ (by decide : 0 < 128)]

/-- The mirror's shift/mod test is exactly the bitmap bit test. -/
theorem zero_bit_equiv (word b : Nat) :
    ((word >>> b) % 2 == 0) = !word.testBit b := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  rw [Nat.mod_two_eq_zero_iff_testBit_zero, Nat.testBit_shiftRight]
  simp

/-- Observable replay state at an allocated keypair identity. -/
def counterAt (w : World) (kp : KeypairId) : Option ReplayCounter :=
  (w.k.wg.bind fun d => d.keypairs.get? kp).map (·.receivingCounter)

@[simp] theorem record_counterAt (w : World) (d : Decision) (b : Bool) (kp : KeypairId) :
    counterAt (record w d b) kp = counterAt w kp := rfl

@[simp] theorem recordCmp_counterAt (w : World) (d : Decision) (outcome : Bool)
    (a b : Int) (kp : KeypairId) :
    counterAt (recordCmp w d outcome a b) kp = counterAt w kp := rfl

@[simp] theorem recordCmp_k (w : World) (d : Decision) (outcome : Bool) (a b : Int) :
    (recordCmp w d outcome a b).k = w.k := rfl

@[simp] theorem clearRecords_counterAt (w : World) (xs : List Nat) (kp : KeypairId) :
    counterAt (clearRecords w xs) kp = counterAt w kp := by
  unfold counterAt
  rw [clearRecords_k]

@[simp] theorem counterAt_store (w : World) (d : Device) (kp : KeypairId) (k : Keypair)
    (hd : w.k.wg = some d) :
    counterAt (store w kp k) kp = some k.receivingCounter := by
  simp [counterAt, store, hd]

@[simp] theorem record_k (w : World) (d : Decision) (b : Bool) :
    (record w d b).k = w.k := rfl

/-- Projection of the exact C execution onto the pure window step. -/
theorem cExecution_refines_step (w : World) (d : Device) (kp : KeypairId)
    (k : Keypair) (nonce : Nat) (hd : w.k.wg = some d)
    (hk : d.keypairs.get? kp = some k) :
    (cExecution kp nonce k w).1 = (step k.receivingCounter nonce).1 ∧
    counterAt (cExecution kp nonce k w).2 kp = some (step k.receivingCounter nonce).2 := by
  have hlookup : counterAt w kp = some k.receivingCounter := by
    change d.keypairs[kp]? = some k at hk
    simp [counterAt, hd, hk]
  by_cases he : eligible k.receivingCounter nonce
  · have h1 : ¬ k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES + 1 := by have := he.1; omega
    have h2 : ¬ nonce ≥ REJECT_AFTER_MESSAGES := by have := he.2.1; omega
    have h3 : ¬8128 + (nonce + 1) < k.receivingCounter.counter := by have := he.2.2; omega
    rw [step, if_pos he]
    by_cases h4 : nonce + 1 > k.receivingCounter.counter
    · simp [cExecution, h1, h2, h3, h4, fresh, prepared, update,
        zero_bit_equiv, Nat.max_eq_right (by omega : k.receivingCounter.counter ≤ nonce + 1),
        counterAt, store, record, recordCmp, clearRecords_k, hd]
    · simp [cExecution, h1, h2, h3, h4, fresh, prepared, update,
        zero_bit_equiv, Nat.max_eq_left (by omega : nonce + 1 ≤ k.receivingCounter.counter),
        counterAt, store, record, recordCmp, hd]
  · rw [step, if_neg he]
    by_cases h1 : k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES + 1
    · simp [cExecution, h1, hlookup]
    · by_cases h2 : nonce ≥ REJECT_AFTER_MESSAGES
      · simp [cExecution, h1, h2, hlookup]
      · have h3 : 8128 + (nonce + 1) < k.receivingCounter.counter := by unfold eligible at he; omega
        simp [cExecution, h1, h2, h3, hlookup]

/-- S2: the fixed mirror's successful run returns exactly the C-rule result
and leaves exactly the C-rule replay state. The array-shape premise makes
explicit the C structure invariant not enforced by the mirror's raw type. -/
theorem S2 (w : World) (d : Device) (kp : KeypairId) (k : Keypair) (nonce : Nat)
    (hd : w.k.wg = some d) (hk : d.keypairs.get? kp = some k)
    (hsize : k.receivingCounter.backtrack.size = 128) :
    ∃ w', (counterValidate kp nonce).run w = .ok ((step k.receivingCounter nonce).1, w') ∧
      counterAt w' kp = some (step k.receivingCounter nonce).2 := by
  have hex := counterValidate_execution w d kp k nonce hd hk hsize
  have hp := cExecution_refines_step w d kp k nonce hd hk
  refine ⟨(cExecution kp nonce k w).2, ?_, hp.2⟩
  rw [hex, ← hp.1]

theorem step_accepts_iff (c : ReplayCounter) (nonce : Nat) :
    (step c nonce).1 = true ↔ eligible c nonce ∧
      (prepared c (nonce + 1))[slot (nonce + 1)]!.testBit (bit (nonce + 1)) = false := by
  by_cases he : eligible c nonce
  · rw [step, if_pos he]
    dsimp only [fresh]
    cases hb : (prepared c (nonce + 1))[slot (nonce + 1)]!.testBit (bit (nonce + 1)) with
    | false => exact ⟨fun _ => ⟨he, rfl⟩, fun _ => rfl⟩
    | true => exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h.2⟩
  · rw [step, if_neg he]
    simp [he]

/-- S2's acceptance characterization, stated directly for the mirror.
The bit is read after the C's advancing clears; the lower edge is inclusive. -/
theorem S2_acceptance (w : World) (d : Device) (kp : KeypairId) (k : Keypair) (nonce : Nat)
    (hd : w.k.wg = some d) (hk : d.keypairs.get? kp = some k)
    (hsize : k.receivingCounter.backtrack.size = 128) :
    (∃ w', (counterValidate kp nonce).run w = .ok (true, w')) ↔
      eligible k.receivingCounter nonce ∧
      (prepared k.receivingCounter (nonce + 1))[slot (nonce + 1)]!.testBit (bit (nonce + 1)) = false := by
  obtain ⟨w', hrun, _⟩ := S2 w d kp k nonce hd hk hsize
  rw [← step_accepts_iff]
  constructor
  · rintro ⟨other, hother⟩
    rw [hrun] at hother
    exact congrArg Prod.fst (Except.ok.inj hother)
  · intro h
    exact ⟨w', by simpa only [h] using hrun⟩

/-- S2's accepted-state update, stated directly for the mirror. -/
theorem S2_update (w w' : World) (d : Device) (kp : KeypairId) (k : Keypair) (nonce : Nat)
    (hd : w.k.wg = some d) (hk : d.keypairs.get? kp = some k)
    (hsize : k.receivingCounter.backtrack.size = 128)
    (hrun : (counterValidate kp nonce).run w = .ok (true, w')) :
    counterAt w' kp = some (update k.receivingCounter nonce) := by
  obtain ⟨other, hother, hcounter⟩ := S2 w d kp k nonce hd hk hsize
  rw [hrun] at hother
  have hp := Except.ok.inj hother
  have hw : w' = other := congrArg Prod.snd hp
  have hb : (step k.receivingCounter nonce).1 = true := (congrArg Prod.fst hp).symm
  have he := (step_accepts_iff _ _).mp hb |>.1
  rw [hw]
  simpa only [step, if_pos he] using hcounter

end Leanux.Proofs.WG.CounterWindow
