import Leanux.Spikes.Refinement

/-! Acceptance observations over the unchanged state and exception monad.
The additional state is proof-side history; erasing it preserves the complete
mirror state, result, and failure, rather than only a counter projection. -/
namespace Leanux.Spikes.Ghost
open Leanux Leanux.WG Leanux.Spikes.Window

structure AcceptedEvent where
  /-- The lifetime identity, rather than the device-local store index. -/
  keypair : Nat
  nonce : Nat
  deriving Repr, DecidableEq

abbrev History := List AcceptedEvent
abbrev GhostM := StateT History M

@[simp] theorem except_error_bind {α β : Type} (e : Stop) (f : α → Except Stop β) :
    (Except.error e >>= f) = .error e := rfl

@[simp] theorem mirror_throw_run (e : Stop) (w : World) :
    (throw e : M α).run w = .error e := rfl

@[simp] theorem liftM_eq_lift (a : M α) : (liftM a : GhostM α) = StateT.lift a := rfl

def eraseResult {α : Type} : Except Stop ((α × History) × World) → Except Stop (α × World)
  | .error e => .error e
  | .ok ((a, _), w) => .ok (a, w)

/-- Equality after forgetting only the additional history. -/
def Erases (logged : GhostM α) (original : M α) : Prop :=
  ∀ history world, eraseResult ((logged.run history).run world) = original.run world

theorem erases_pure (a : α) : Erases (pure a) (pure a) := by
  intro history world
  rfl

theorem erases_lift (a : M α) : Erases (StateT.lift a) a := by
  intro history world
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, except_pure]
  cases a.run world <;> rfl

theorem erases_liftM (a : M α) : Erases (liftM a) a := erases_lift a

theorem erases_ite (p : Prop) [Decidable p]
    {gt ge : GhostM α} {ot oe : M α}
    (ht : p → Erases gt ot) (he : ¬ p → Erases ge oe) :
    Erases (if p then gt else ge) (if p then ot else oe) := by
  by_cases hp : p
  · simpa only [if_pos hp] using ht hp
  · simpa only [if_neg hp] using he hp

theorem erases_bind {logged : GhostM α} {original : M α}
    {lg : α → GhostM β} {og : α → M β}
    (ha : Erases logged original) (hb : ∀ a, Erases (lg a) (og a)) :
    Erases (logged >>= lg) (original >>= og) := by
  intro history world
  simp only [StateT.run_bind]
  have hm := ha history world
  cases he : (logged.run history).run world with
  | error e =>
    simp only [he, eraseResult] at hm
    simp [← hm, eraseResult]
  | ok out =>
    rcases out with ⟨⟨a, h⟩, w⟩
    simp only [he, eraseResult] at hm
    simpa [← hm, eraseResult, except_ok_bind] using hb a h w

theorem erases_bind_return {logged : GhostM α} {original : M α}
    {lg : α → GhostM α} (ha : Erases logged original)
    (hb : ∀ a, Erases (lg a) (pure a)) : Erases (logged >>= lg) original := by
  simpa only [bind_pure] using erases_bind ha hb

theorem erases_map {logged : GhostM α} {original : M α}
    (f : α → β) (h : Erases logged original) :
    Erases (f <$> logged) (f <$> original) := by
  simpa only [map_eq_pure_bind] using erases_bind h (fun a => erases_pure (f a))

theorem erases_forIn (xs : List α) (b : β)
    (logged : α → β → GhostM (ForInStep β))
    (original : α → β → M (ForInStep β))
    (h : ∀ a b, Erases (logged a b) (original a b)) :
    Erases (forIn xs b logged) (forIn xs b original) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using erases_pure b
  | cons a xs ih =>
    rw [List.forIn_cons, List.forIn_cons]
    apply erases_bind (h a b)
    intro s
    cases s with
    | done b => exact erases_pure b
    | yield b => exact ih b

theorem erases_range (r : Std.Legacy.Range) (b : β)
    (logged : Nat → β → GhostM (ForInStep β))
    (original : Nat → β → M (ForInStep β))
    (h : ∀ a b, Erases (logged a b) (original a b)) :
    Erases (forIn r b logged) (forIn r b original) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact erases_forIn _ b logged original h

def emit (e : AcceptedEvent) : GhostM Unit :=
  modifyThe History (· ++ [e])

theorem erases_emit (e : AcceptedEvent) : Erases (emit e) (pure ()) := by
  intro history world
  rfl

/-- Execute the actual validator once and record exactly its true results. -/
def counterLogged (kp : KeypairId) (nonce : Nat) : GhostM Bool := do
  let k ← StateT.lift (getKeypair kp)
  let ok ← StateT.lift (counterValidate kp nonce)
  if ok then emit ⟨k.internalId, nonce⟩
  return ok

/-- A getter before this getter-led function is redundant, including errors. -/
theorem getKeypair_before_validate (kp : KeypairId) (nonce : Nat) :
    (do let _ ← getKeypair kp; counterValidate kp nonce) = counterValidate kp nonce := by
  funext w
  change (do let _ ← getKeypair kp; counterValidate kp nonce).run w =
    (counterValidate kp nonce).run w
  cases hd : w.k.wg with
  | none => simp [getKeypair, getDev, getK, hd, counterValidate, invariant, StateT.run_bind, StateT.run_get]
  | some d =>
    cases hk : d.keypairs[kp]? with
    | none => simp [getKeypair, getDev, getK, hd, hk, counterValidate, invariant, StateT.run_bind, StateT.run_get]
    | some k =>
      have hg := getKeypair_run w d kp k hd hk
      simp only [StateT.run_bind, hg, except_ok_bind]

/-- The logged validator erases to the unchanged executable validator. -/
theorem counterLogged_erases (kp : KeypairId) (nonce : Nat) :
    Erases (counterLogged kp nonce) (counterValidate kp nonce) := by
  rw [← getKeypair_before_validate kp nonce]
  unfold counterLogged
  apply erases_bind (erases_lift (getKeypair kp))
  intro k
  apply erases_bind_return (erases_lift (counterValidate kp nonce))
  intro ok
  cases ok with
  | false => exact erases_pure false
  | true =>
    exact erases_bind (erases_emit _) (fun _ => erases_pure true)

/-- The event's data and multiplicity are tied to one actual successful call.
This is stronger than erasure alone, which would also allow an empty log. -/
theorem counterLogged_run (kp : KeypairId) (nonce : Nat) (history : History)
    (w w' : World) (d : Device) (k : Keypair) (ok : Bool)
    (hd : w.k.wg = some d) (hk : d.keypairs.get? kp = some k)
    (hr : (counterValidate kp nonce).run w = .ok (ok, w')) :
    ((counterLogged kp nonce).run history).run w =
      .ok ((ok, if ok then history ++ [⟨k.internalId, nonce⟩] else history), w') := by
  have hg := getKeypair_run w d kp k hd hk
  simp only [counterLogged, StateT.run_bind, StateT.run_lift, hg, hr,
    except_ok_bind, StateT.run_pure, except_pure]
  cases ok <;> rfl

end Leanux.Spikes.Ghost
