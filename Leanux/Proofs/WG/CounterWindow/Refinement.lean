import Leanux.Proofs.WG.CounterWindow.Model

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.CounterWindow
open Leanux Leanux.WG

@[simp] theorem except_pure {α : Type} (a : α) :
    (pure a : Except Stop α) = .ok a := rfl

@[simp] theorem except_ok_bind {α β : Type} (a : α) (f : α → Except Stop β) :
    (Except.ok a >>= f) = f a := rfl

/-- The mirror's branch recorder updates only the actual ambient state. -/
def record (a : Ambient) (d : Decision) (outcome : Bool) : Ambient :=
  { a with steps := a.steps.push { decision := d, outcome, netRx := a.netRxSection } }

@[simp] theorem branch_run (a : Ambient) (d : Decision) (outcome : Bool) :
    (AmbientM.branch d outcome).run a = .ok (outcome, record a d outcome) := rfl

/-- A comparison record retains the mirror's two concrete operands. -/
def recordCmp (a : Ambient) (d : Decision) (outcome : Bool) (x y : Int) : Ambient :=
  { a with steps := a.steps.push { decision := d, outcome, operands := some (x, y), netRx := a.netRxSection } }

@[simp] theorem branchCmp_run (a : Ambient) (d : Decision) (outcome : Bool) (x y : Int) :
    (AmbientM.branchCmp d outcome x y).run a = .ok (outcome, recordCmp a d outcome x y) := rfl

/-- The word-clearing body uses the ambient recorder and no subsystem state. -/
def clearBody (current : Nat) (i : Nat) (a : Array Nat) : AmbientM (ForInStep (Array Nat)) := do
  _ ← branch .ctrClearIter true
  let j := (i + current) % 128
  if j ≥ a.size then
    let _ : Unit ← invariant s!"backtrack[{j}] beyond the bitmap"
    return .yield (a.set! j 0)
  else return .yield (a.set! j 0)

/-- All bookkeeping effects of the loop, separated from its bitmap effect. -/
def clearRecords : Ambient → List Nat → Ambient
  | a, [] => a
  | a, _ :: xs => clearRecords (record a .ctrClearIter true) xs

/-- The mirror's monadic clear loop performs exactly the pure list of clears.
It cannot stop when the replay bitmap has the C shape. -/
theorem clear_loop_run (a : Array Nat) (current : Nat) (xs : List Nat)
    (ambient : Ambient) (hsize : a.size = 128) :
    (forIn xs a (clearBody current)).run ambient =
      .ok (clear a current xs, clearRecords ambient xs) := by
  induction xs generalizing a ambient with
  | nil => rfl
  | cons i xs ih =>
    have hj : ¬(i + current) % 128 ≥ a.size := by rw [hsize]; omega
    simp only [List.forIn_cons, clearBody, hj, ite_false, bind_pure_comp,
      StateT.run_bind]
    change (forIn xs (a.set! ((i + current) % 128) 0) (clearBody current)).run
      (record ambient .ctrClearIter true) = _
    exact ih _ _ (by simp [hsize])

/-- A state lift commutes with list iteration. This is the transformer law
used at the actual ambient-only loop, not a per-operation frame. -/
private theorem forIn_lift {σ α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (xs : List α) (b : β) (f : α → β → m (ForInStep β)) :
    (forIn xs b (fun x y => StateT.lift (f x y)) : StateT σ m β) =
      StateT.lift (forIn xs b f) := by
  induction xs generalizing b with
  | nil =>
    apply StateT.ext
    intro s
    simp [List.forIn_nil]
  | cons x xs ih =>
    apply StateT.ext
    intro s
    simp only [List.forIn_cons, StateT.run_bind_lift, StateT.run_lift, bind_assoc]
    apply bind_congr
    intro step
    cases step with
    | done y => simp
    | yield y => exact congrFun (ih y) s

@[simp] theorem getKeypair_run (w : WGWorld) (ambient : Ambient) (d : Device)
    (kp : KeypairId) (k : Keypair)
    (hd : w.dev = some d) (hk : d.keypairs.get? kp = some k) :
    ((getKeypair kp).run w).run ambient = .ok ((k, w), ambient) := by
  change d.keypairs[kp]? = some k at hk
  simp [getKeypair, getDev, hd, hk]

def store (w : WGWorld) (kp : KeypairId) (k : Keypair) : WGWorld :=
  { w with dev := w.dev.map fun d => { d with keypairs := d.keypairs.insert kp k } }

@[simp] theorem setKeypair_run (w : WGWorld) (ambient : Ambient) (kp : KeypairId) (k : Keypair) :
    ((setKeypair kp k).run w).run ambient = .ok (((), store w kp k), ambient) := rfl

/-- A direct operational transcription of receive.c after its keypair lookup.
The result has the actual nested WG and ambient execution tuple. -/
def cExecution (kp : KeypairId) (nonce : Nat) (k : Keypair)
    (w : WGWorld) (ambient : Ambient) : (Bool × WGWorld) × Ambient :=
  let c := k.receivingCounter
  let ambient := recordCmp ambient .ctrRejectCounter (c.counter ≥ REJECT_AFTER_MESSAGES + 1)
    c.counter (REJECT_AFTER_MESSAGES + 1)
  if c.counter ≥ REJECT_AFTER_MESSAGES + 1 then ((false, w), ambient) else
  let ambient := recordCmp ambient .ctrRejectTheirs (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES
  if nonce ≥ REJECT_AFTER_MESSAGES then ((false, w), ambient) else
  let n := nonce + 1
  let ambient := record ambient .ctrTooOld (8128 + n < c.counter)
  if 8128 + n < c.counter then ((false, w), ambient) else
  let ambient := record ambient .ctrAdvance (n > c.counter)
  let (a, high, ambient) := if n > c.counter then
      let xs := List.range' 1 (min (n / 64 - c.counter / 64) 128)
      (clear c.backtrack (c.counter / 64) xs, n,
        record (clearRecords ambient xs) .ctrClearIter false)
    else (c.backtrack, c.counter, ambient)
  let word := a[slot n]!
  let c' : ReplayCounter :=
    { counter := high
      backtrack := a.set! (slot n) (word ||| (1 <<< bit n)) }
  let w := store w kp { k with receivingCounter := c' }
  (((word >>> bit n) % 2 == 0, w), ambient)

/-- The word-clearing loop in the mirror is the C loop lifted from AmbientM. -/
theorem mirror_clear_loop (a : Array Nat) (current top : Nat)
    (w : WGWorld) (ambient : Ambient) (hsize : a.size = 128) :
    (((forIn [1:top + 1] a (fun i a => do
      _ ← branch .ctrClearIter true
      let j := (i + current) % 128
      if j ≥ a.size then
        let _ : Unit ← invariant s!"backtrack[{j}] beyond the bitmap"
        return .yield (a.set! j 0)
      else return .yield (a.set! j 0)) : WG.M _).run w).run ambient) =
      .ok ((clear a current (List.range' 1 top), w), clearRecords ambient (List.range' 1 top)) := by
  have hbody : (fun (i : Nat) (a : Array Nat) => (do
      _ ← branch .ctrClearIter true
      let j := (i + current) % 128
      if j ≥ a.size then
        let _ : Unit ← invariant s!"backtrack[{j}] beyond the bitmap"
        return .yield (a.set! j 0)
      else return .yield (a.set! j 0)) : Nat → Array Nat → WG.M (ForInStep (Array Nat))) =
      (fun i a => StateT.lift (clearBody current i a)) := by
    funext i a g env
    by_cases hj : (i + current) % 128 ≥ a.size <;>
      simp [clearBody, hj, branch, AmbientM.branch, invariant, AmbientM.invariant] <;> rfl
  rw [hbody, Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [forIn_lift, StateT.run_lift, StateT.run_bind]
  have h := clear_loop_run a current (List.range' 1 top) ambient hsize
  simp [Std.Legacy.Range.size, h]

/-- Exact successful execution equality for the fixed mirror's validator. -/
theorem counterValidate_execution (w : WGWorld) (ambient : Ambient) (d : Device)
    (kp : KeypairId) (k : Keypair) (nonce : Nat) (hd : w.dev = some d)
    (hk : d.keypairs.get? kp = some k) (hsize : k.receivingCounter.backtrack.size = 128) :
    ((counterValidate kp nonce).run w).run ambient = .ok (cExecution kp nonce k w ambient) := by
  change d.keypairs[kp]? = some k at hk
  by_cases h1 : k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES + 1
  · simp [counterValidate, getKeypair, getDev, hd, hk, WG.orM, h1, cExecution,
      branchCmp, AmbientM.branchCmp, recordCmp, StateT.run_bind]
    rfl
  · by_cases h2 : nonce ≥ REJECT_AFTER_MESSAGES
    · simp [counterValidate, getKeypair, getDev, hd, hk, WG.orM, h1, h2, cExecution,
        branchCmp, AmbientM.branchCmp, recordCmp, StateT.run_bind]
      rfl
    · by_cases h3 : 8128 + (nonce + 1) < k.receivingCounter.counter
      · simp [counterValidate, getKeypair, getDev, hd, hk, WG.orM, h1, h2, h3,
          cExecution, COUNTER_WINDOW_SIZE, branch, branchCmp, AmbientM.branch,
          AmbientM.branchCmp, record, recordCmp, StateT.run_bind]
        rfl
      · by_cases h4 : nonce + 1 > k.receivingCounter.counter
        · simp only [counterValidate, StateT.run_bind, getKeypair_run w ambient d kp k hd hk,
            except_ok_bind, WG.orM, h1, h2, h3, h4, decide_false, decide_true,
            ite_false, ite_true, COUNTER_WINDOW_SIZE,
            COUNTER_BITS_TOTAL, BITS_PER_LONG, cExecution]
          simp only [show 8192 / 64 = 128 from rfl]
          have hloop := mirror_clear_loop _ (k.receivingCounter.counter / 64)
            (min ((nonce + 1) / 64 - k.receivingCounter.counter / 64) 128) w
            (record (record (recordCmp (recordCmp ambient .ctrRejectCounter false k.receivingCounter.counter
              (REJECT_AFTER_MESSAGES + 1)) .ctrRejectTheirs false nonce REJECT_AFTER_MESSAGES)
              .ctrTooOld false) .ctrAdvance true) hsize
          simp only [branch, branchCmp, StateT.run_monadLift, monadLift_self, StateT.run_bind,
            branch_run, branchCmp_run, except_ok_bind, StateT.run_pure, except_pure,
            Bool.false_eq_true, ite_false, ite_true]
          simp only [branch] at hloop
          rw [hloop]
          simp only [except_ok_bind]
          rw [Array.getElem?_eq_some_getElem!]
          · rfl
          · simp [hsize, Nat.mod_lt _ (by decide : 0 < 128)]
        · simp only [counterValidate, StateT.run_bind, getKeypair_run w ambient d kp k hd hk,
            except_ok_bind, WG.orM, h1, h2, h3, h4, decide_false,
            ite_false, COUNTER_WINDOW_SIZE,
            COUNTER_BITS_TOTAL, BITS_PER_LONG, cExecution]
          simp only [show 8192 / 64 = 128 from rfl]
          simp only [branch, branchCmp, StateT.run_monadLift, monadLift_self, StateT.run_bind,
            branch_run, branchCmp_run, except_ok_bind, StateT.run_pure, except_pure,
            Bool.false_eq_true, ite_false]
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
def counterAt (w : WGWorld) (kp : KeypairId) : Option ReplayCounter :=
  (w.dev.bind fun d => d.keypairs.get? kp).map (·.receivingCounter)

@[simp] theorem counterAt_store (w : WGWorld) (d : Device) (kp : KeypairId) (k : Keypair)
    (hd : w.dev = some d) :
    counterAt (store w kp k) kp = some k.receivingCounter := by
  simp [counterAt, store, hd]

/-- Projection of the exact C execution onto the pure window step. -/
theorem cExecution_refines_step (w : WGWorld) (ambient : Ambient) (d : Device) (kp : KeypairId)
    (k : Keypair) (nonce : Nat) (hd : w.dev = some d)
    (hk : d.keypairs.get? kp = some k) :
    (cExecution kp nonce k w ambient).1.1 = (step k.receivingCounter nonce).1 ∧
    counterAt (cExecution kp nonce k w ambient).1.2 kp = some (step k.receivingCounter nonce).2 := by
  have hlookup : counterAt w kp = some k.receivingCounter := by
    change d.keypairs[kp]? = some k at hk
    simp [counterAt, hd, hk]
  by_cases he : eligible k.receivingCounter nonce
  · have h1 : ¬ k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES + 1 := by have := he.1; omega
    have h2 : ¬ nonce ≥ REJECT_AFTER_MESSAGES := by have := he.2.1; omega
    have h3 : ¬8128 + (nonce + 1) < k.receivingCounter.counter := by have := he.2.2; omega
    rw [step, ite_eq_left he]
    by_cases h4 : nonce + 1 > k.receivingCounter.counter
    · simp [cExecution, h1, h2, h3, h4, fresh, prepared, update,
        zero_bit_equiv, Nat.max_eq_right (by omega : k.receivingCounter.counter ≤ nonce + 1),
        counterAt, store, record, recordCmp, hd]
    · simp [cExecution, h1, h2, h3, h4, fresh, prepared, update,
        zero_bit_equiv, Nat.max_eq_left (by omega : nonce + 1 ≤ k.receivingCounter.counter),
        counterAt, store, record, recordCmp, hd]
  · rw [step, ite_eq_right he]
    by_cases h1 : k.receivingCounter.counter ≥ REJECT_AFTER_MESSAGES + 1
    · simp [cExecution, h1, hlookup]
    · by_cases h2 : nonce ≥ REJECT_AFTER_MESSAGES
      · simp [cExecution, h1, h2, hlookup]
      · have h3 : 8128 + (nonce + 1) < k.receivingCounter.counter := by unfold eligible at he; omega
        simp [cExecution, h1, h2, h3, hlookup]

/-- S2: the fixed mirror's successful run returns exactly the C-rule result
and leaves exactly the C-rule replay state. The array-shape premise makes
explicit the C structure invariant not enforced by the mirror's raw type. -/
theorem S2 (w : WGWorld) (ambient : Ambient) (d : Device) (kp : KeypairId) (k : Keypair) (nonce : Nat)
    (hd : w.dev = some d) (hk : d.keypairs.get? kp = some k)
    (hsize : k.receivingCounter.backtrack.size = 128) :
    ∃ w' ambient', ((counterValidate kp nonce).run w).run ambient = .ok (((step k.receivingCounter nonce).1, w'), ambient') ∧
      counterAt w' kp = some (step k.receivingCounter nonce).2 := by
  have hex := counterValidate_execution w ambient d kp k nonce hd hk hsize
  have hp := cExecution_refines_step w ambient d kp k nonce hd hk
  refine ⟨(cExecution kp nonce k w ambient).1.2, (cExecution kp nonce k w ambient).2, ?_, hp.2⟩
  rw [hex, ← hp.1]

theorem step_accepts_iff (c : ReplayCounter) (nonce : Nat) :
    (step c nonce).1 = true ↔ eligible c nonce ∧
      (prepared c (nonce + 1))[slot (nonce + 1)]!.testBit (bit (nonce + 1)) = false := by
  by_cases he : eligible c nonce
  · rw [step, ite_eq_left he]
    dsimp only [fresh]
    cases hb : (prepared c (nonce + 1))[slot (nonce + 1)]!.testBit (bit (nonce + 1)) with
    | false => exact ⟨fun _ => ⟨he, rfl⟩, fun _ => rfl⟩
    | true => exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h.2⟩
  · rw [step, ite_eq_right he]
    simp [he]

/-- S2's acceptance characterization, stated directly for the mirror.
The bit is read after the C's advancing clears; the lower edge is inclusive. -/
theorem S2_acceptance (w : WGWorld) (ambient : Ambient) (d : Device) (kp : KeypairId) (k : Keypair) (nonce : Nat)
    (hd : w.dev = some d) (hk : d.keypairs.get? kp = some k)
    (hsize : k.receivingCounter.backtrack.size = 128) :
    (∃ w' ambient', ((counterValidate kp nonce).run w).run ambient = .ok ((true, w'), ambient')) ↔
      eligible k.receivingCounter nonce ∧
      (prepared k.receivingCounter (nonce + 1))[slot (nonce + 1)]!.testBit (bit (nonce + 1)) = false := by
  obtain ⟨w', ambient', hrun, _⟩ := S2 w ambient d kp k nonce hd hk hsize
  rw [← step_accepts_iff]
  constructor
  · rintro ⟨other, otherAmbient, hother⟩
    rw [hrun] at hother
    exact congrArg (fun out => out.1.1) (Except.ok.inj hother)
  · intro h
    exact ⟨w', ambient', by simpa only [h] using hrun⟩

/-- S2's accepted-state update, stated directly for the mirror. -/
theorem S2_update (w w' : WGWorld) (ambient ambient' : Ambient) (d : Device) (kp : KeypairId) (k : Keypair) (nonce : Nat)
    (hd : w.dev = some d) (hk : d.keypairs.get? kp = some k)
    (hsize : k.receivingCounter.backtrack.size = 128)
    (hrun : ((counterValidate kp nonce).run w).run ambient = .ok ((true, w'), ambient')) :
    counterAt w' kp = some (update k.receivingCounter nonce) := by
  obtain ⟨other, otherAmbient, hother, hcounter⟩ := S2 w ambient d kp k nonce hd hk hsize
  rw [hrun] at hother
  have hp := Except.ok.inj hother
  have hw : w' = other := congrArg (fun out => out.1.2) hp
  have hb : (step k.receivingCounter nonce).1 = true := (congrArg (fun out => out.1.1) hp).symm
  have he := (step_accepts_iff _ _).mp hb |>.1
  rw [hw]
  simpa only [step, ite_eq_left he] using hcounter

end Leanux.Proofs.WG.CounterWindow
