import Leanux.Proofs.WG.Lifetimes.MaintenanceCalls

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! All-input replay-counter access observation. Malformed bitmaps retain
original errors; no bitmap-size or counter-window validity premise is used. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def counterValidatePrefix (kp : KeypairId) (theirs : Nat) : MixedM Bool := do
  let k ← getKeypairPrefix kp
  let c := k.receivingCounter
  -- `counter->counter >= REJECT_AFTER_MESSAGES + 1 || their_counter >= REJECT_AFTER_MESSAGES`
  if ← liftWGPrefix (WG.orM (branchCmp .ctrRejectCounter (c.counter ≥ REJECT_AFTER_MESSAGES + 1) c.counter (REJECT_AFTER_MESSAGES + 1))
      (branchCmp .ctrRejectTheirs (theirs ≥ REJECT_AFTER_MESSAGES) theirs REJECT_AFTER_MESSAGES)) then return false
  let theirs := theirs + 1   -- ++their_counter
  if ← liftWGPrefix (branch .ctrTooOld (COUNTER_WINDOW_SIZE + theirs < c.counter)) then return false
  let words := COUNTER_BITS_TOTAL / BITS_PER_LONG
  let index := theirs / BITS_PER_LONG   -- their_counter >> ilog2(BITS_PER_LONG)
  let mut backtrack := c.backtrack
  let mut counter := c.counter
  if ← liftWGPrefix (branch .ctrAdvance (theirs > c.counter)) then
    let indexCurrent := c.counter / BITS_PER_LONG
    let top := min (index - indexCurrent) words
    for i in [1:top + 1] do
      _ ← liftWGPrefix (branch .ctrClearIter true)
      let j := (i + indexCurrent) % words
      if j ≥ backtrack.size then liftWGPrefix (invariant s!"backtrack[{j}] beyond the bitmap")
      backtrack := backtrack.set! j 0
    _ ← liftWGPrefix (branch .ctrClearIter false)
    counter := theirs
  -- `!test_and_set_bit(their_counter & (BITS_PER_LONG - 1), &backtrack[index & (words - 1)])`
  let index := index % words
  let bit := theirs % BITS_PER_LONG
  let some word := backtrack[index]? | liftWGPrefix (invariant s!"backtrack[{index}] beyond the bitmap")
  backtrack := backtrack.set! index (word ||| (1 <<< bit))
  setKeypairPrefix kp { k with receivingCounter := { counter, backtrack } }
  return (word >>> bit) % 2 == 0

theorem counterValidatePrefix_erases (kp : KeypairId) (nonce : Nat) :
    ErasesStatePrefix (counterValidatePrefix kp nonce) (counterValidate kp nonce) := by
  unfold counterValidatePrefix counterValidate
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | with_reducible exact getKeypairPrefix_erases _
    | with_reducible exact setKeypairPrefix_erases _ _
    | with_reducible exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | split
    | (solve | simp_all)
    | (with_reducible intro x; try dsimp only)

  all_goals try simp_all only [Option.some.injEq]
  all_goals first
    | exact setKeypairPrefix_erases _ _
    | exact erasesStatePrefix_pure _
    | exact erasesStatePrefix_lift _

theorem counterValidatePrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (kp : KeypairId) (nonce : Nat) :
    AmbientSpec I P (counterValidatePrefix kp nonce) (fun _ => P) := by
  unfold counterValidatePrefix
  apply StatePrefixEnsures.bind (c.getKeypair P kp)
  intro k
  let Q := fun s : IdentityView => P s ∧ s.2.1 kp = some k.internalId
  have hset (r : ReplayCounter) : AmbientSpec I Q (setKeypairPrefix kp {k with receivingCounter := r}) (fun _ => P) := c.setKeypair P kp {k with receivingCounter := r}
  have hloop (r : Std.Legacy.Range) (a : Array Nat) (f : Nat → Array Nat → MixedM (ForInStep (Array Nat)))
      (hf : ∀ i a, AmbientSpec I Q (f i a) (fun _ => Q)) :
      AmbientSpec I Q (forIn r a f) (fun _ => Q) :=
    by
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      exact StatePrefixEnsures.forInInvariant _ a f
        (fun _ h w (_ : Ambient) => I h w ∧ Q (identityView w)) LifetimeEvent.Safe
        (fun _ h w _ hi => c.safe h w hi.1) hf
  apply StatePrefixEnsures.bind (c.store Q _ (orM_sameView
    (by intro initial; exact hoare_liftAmbient (AmbientM.branchCmp _ _ _ _) (fun w => wgStoreView w = initial))
    (by intro initial; exact hoare_liftAmbient (AmbientM.branchCmp _ _ _ _) (fun w => wgStoreView w = initial))))
  intro rejected
  split
  · exact AmbientContracts.forget (c.pure Q false) (fun _ _ hi => hi.1)
  · apply StatePrefixEnsures.bind (c.branch Q _ _)
    intro old
    split
    · exact AmbientContracts.forget (c.pure Q false) (fun _ _ hi => hi.1)
    · repeat' first
        | with_reducible exact hset _
        | with_reducible exact c.pure P _
        | with_reducible exact c.branch Q _ _
        | with_reducible exact c.pure Q _
        | with_reducible exact c.invariant Q _
        | exact AmbientContracts.forget (c.invariant Q _) (fun _ _ hi => hi.1)
        | apply hloop
        | with_reducible apply StatePrefixEnsures.bind
        | split
        | (with_reducible intro x; try dsimp only)

theorem counterValidatePrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (kp : KeypairId) (nonce : Nat) :
    ProductAmbientSpec I P (liftWGObserver (counterValidatePrefix kp nonce)) (fun _ => P) := by
  have transport {α β : Type} (xs : List α) (init : β) (f : α → β → MixedM (ForInStep β)) :
      liftWGObserver (forIn xs init f) = forIn xs init (fun x b => liftWGObserver (f x b)) := by
    induction xs generalizing init with
    | nil => simp only [List.forIn_nil, liftWGObserver_pure]
    | cons x xs ih =>
      simp only [List.forIn_cons, liftWGObserver_bind]
      congr 1
      funext step
      cases step with
      | done b => exact liftWGObserver_pure b
      | yield b => exact ih b
  have branch (Q : IdentityView → Prop) (d : Decision) (b : Bool) :
      ProductAmbientSpec I Q (liftWGObserver (liftWGPrefix (Leanux.branch d b))) (fun _ => Q) :=
    c.nativeStore Q _ (by intro initial; exact hoare_liftAmbient (AmbientM.branch d b) _)
  have invariant {α : Type} (Q : IdentityView → Prop) (why : String) :
      ProductAmbientSpec I Q (liftWGObserver (liftWGPrefix (Leanux.invariant (α := α) why))) (fun _ => Q) :=
    c.nativeStore Q _ (by intro initial; exact hoare_liftAmbient (AmbientM.invariant why) _)
  unfold counterValidatePrefix
  simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  apply PrefixEnsures.bind (c.getKeypair P kp)
  intro k
  let Q := fun s : IdentityView => P s ∧ s.2.1 kp = some k.internalId
  have hset (r : ReplayCounter) :
      ProductAmbientSpec I Q (liftWGObserver (setKeypairPrefix kp {k with receivingCounter := r})) (fun _ => P) :=
    c.setKeypair P kp {k with receivingCounter := r}
  have hloop (r : Std.Legacy.Range) (a : Array Nat) (f : Nat → Array Nat → MixedM (ForInStep (Array Nat)))
      (hf : ∀ i a, ProductAmbientSpec I Q (liftWGObserver (f i a)) (fun _ => Q)) :
      ProductAmbientSpec I Q (liftWGObserver (forIn r a f)) (fun _ => Q) := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range', transport]
    exact PrefixPreserves.forIn _ a _ (fun h w hi => c.safe h w hi.1) hf
  apply PrefixEnsures.bind (c.nativeStore Q _ (orM_sameView
    (by intro initial; exact hoare_liftAmbient (AmbientM.branchCmp _ _ _ _) (fun w => wgStoreView w = initial))
    (by intro initial; exact hoare_liftAmbient (AmbientM.branchCmp _ _ _ _) (fun w => wgStoreView w = initial))))
  intro rejected
  split
  · exact ProductAmbientContracts.forget (c.pure Q false) (fun _ _ hi => hi.1)
  · apply PrefixEnsures.bind (branch Q _ _)
    intro old
    split
    · exact ProductAmbientContracts.forget (c.pure Q false) (fun _ _ hi => hi.1)
    · repeat' first
        | simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
        | with_reducible exact hset _
        | with_reducible exact c.pure P _
        | with_reducible exact branch Q _ _
        | with_reducible exact c.pure Q _
        | with_reducible exact invariant Q _
        | exact ProductAmbientContracts.forget (invariant Q _) (fun _ _ hi => hi.1)
        | apply hloop
        | with_reducible apply PrefixEnsures.bind
        | split
        | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Lifetimes
