import Leanux.Proofs.WG.Lifetimes.TxStagingCalls

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
  if ← liftPrefix (WG.orM (branch .ctrRejectCounter (c.counter ≥ REJECT_AFTER_MESSAGES + 1))
      (branch .ctrRejectTheirs (theirs ≥ REJECT_AFTER_MESSAGES))) then return false
  let theirs := theirs + 1   -- ++their_counter
  if ← liftPrefix (branch .ctrTooOld (COUNTER_WINDOW_SIZE + theirs < c.counter)) then return false
  let words := COUNTER_BITS_TOTAL / BITS_PER_LONG
  let index := theirs / BITS_PER_LONG   -- their_counter >> ilog2(BITS_PER_LONG)
  let mut backtrack := c.backtrack
  let mut counter := c.counter
  if ← liftPrefix (branch .ctrAdvance (theirs > c.counter)) then
    let indexCurrent := c.counter / BITS_PER_LONG
    let top := min (index - indexCurrent) words
    for i in [1:top + 1] do
      _ ← liftPrefix (branch .ctrClearIter true)
      let j := (i + indexCurrent) % words
      if j ≥ backtrack.size then liftPrefix (invariant s!"backtrack[{j}] beyond the bitmap")
      backtrack := backtrack.set! j 0
    _ ← liftPrefix (branch .ctrClearIter false)
    counter := theirs
  -- `!test_and_set_bit(their_counter & (BITS_PER_LONG - 1), &backtrack[index & (words - 1)])`
  let index := index % words
  let bit := theirs % BITS_PER_LONG
  let some word := backtrack[index]? | liftPrefix (invariant s!"backtrack[{index}] beyond the bitmap")
  backtrack := backtrack.set! index (word ||| (1 <<< bit))
  setKeypairPrefix kp { k with receivingCounter := { counter, backtrack } }
  return (word >>> bit) % 2 == 0

theorem counterValidatePrefix_erases (kp : KeypairId) (nonce : Nat) :
    ErasesPrefix (counterValidatePrefix kp nonce) (counterValidate kp nonce) := by
  unfold counterValidatePrefix counterValidate
  repeat' first
    | with_reducible exact getKeypairPrefix_erases _
    | with_reducible exact setKeypairPrefix_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | split
    | (solve | simp_all)
    | (with_reducible intro x; try dsimp only)

  all_goals simp_all only [Option.some.injEq]
  all_goals first
    | exact setKeypairPrefix_erases _ _
    | exact erasesPrefix_pure _
    | exact erasesPrefix_lift _

theorem counterValidatePrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop)
    (kp : KeypairId) (nonce : Nat) :
    AmbientSpec I P (counterValidatePrefix kp nonce) (fun _ => P) := by
  unfold counterValidatePrefix
  apply PrefixEnsures.bind (c.getKeypair P kp)
  intro k
  let Q := fun s : IdentityView => P s ∧ s.2.1 kp = some k.internalId
  have hset (r : ReplayCounter) : AmbientSpec I Q (setKeypairPrefix kp {k with receivingCounter := r}) (fun _ => P) := c.setKeypair P kp {k with receivingCounter := r}
  have hloop (r : Std.Legacy.Range) (a : Array Nat) (f : Nat → Array Nat → MixedM (ForInStep (Array Nat)))
      (hf : ∀ i a, AmbientSpec I Q (f i a) (fun _ => Q)) :
      AmbientSpec I Q (forIn r a f) (fun _ => Q) :=
    PrefixPreserves.range r a f (fun h w hi => c.safe h w hi.1) hf
  apply PrefixEnsures.bind (c.kernel Q _ (orM_sameKernel (sameKernel_branch _ _) (sameKernel_branch _ _)))
  intro rejected
  split
  · exact AmbientContracts.forget (c.pure Q false) (fun _ _ hi => hi.1)
  · apply PrefixEnsures.bind (c.branch Q _ _)
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
        | with_reducible apply PrefixEnsures.bind
        | split
        | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Lifetimes
