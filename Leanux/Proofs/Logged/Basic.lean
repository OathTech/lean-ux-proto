import Leanux.Proofs.Logged.Ghost
import Leanux.Proofs.WG.CounterWindow.Refinement

/-! Acceptance observations over the mirror's actual monads. The additional
state is proof-side history; erasing it preserves the complete execution,
including both native WG and Ambient endpoints or the exact Stop. -/
namespace Leanux.Proofs.Logged
open Leanux Leanux.WG Leanux.Proofs.WG.CounterWindow

structure AcceptedEvent where
  /-- The lifetime identity, rather than the device-local store index. -/
  keypair : Nat
  nonce : Nat
  deriving Repr, DecidableEq

abbrev History := List AcceptedEvent
abbrev GhostT (m : Type → Type) := StateT History m
abbrev GhostM := GhostT Leanux.M
abbrev WGGhostM := GhostT WG.M

@[simp] theorem except_error_bind {α β : Type} (e : Stop) (f : α → Except Stop β) :
    (Except.error e >>= f) = .error e := rfl

@[simp] theorem mirror_throw_run (e : Stop) (w : World) :
    (throw e : Leanux.M α).run w = .error e := rfl

@[simp] theorem liftM_eq_lift {m : Type → Type} [Monad m] (a : m α) :
    (liftM a : GhostT m α) = StateT.lift a := rfl

def eraseResult {α : Type} : Except Stop ((α × History) × World) → Except Stop (α × World)
  | .error e => .error e
  | .ok ((a, _), w) => .ok (a, w)

/-- Equality after forgetting only the additional history. -/
abbrev Erases {m : Type → Type} [Functor m]
    (logged : GhostT m α) (original : m α) : Prop :=
  ErasesT logged original

/-- Read generic erasure at the actual product-world execution boundary. -/
theorem erases_run {g : GhostM α} {o : Leanux.M α} (h : Erases g o)
    (history : History) (world : World) :
    eraseResult ((g.run history).run world) = o.run world := by
  have he := congrFun (h history) world
  change ((g.run history).run world).map (fun ((a, _), w) => (a, w)) = o.run world at he
  cases hr : (g.run history).run world <;> simpa only [hr, eraseResult, Except.map] using he

/-- Native erasure retains both actual WG and Ambient endpoints. -/
theorem erases_runWG {g : WGGhostM α} {o : WG.M α} (h : Erases g o)
    (history : History) (wg : WGWorld) (ambient : Ambient) :
    (((g.run history).run wg).run ambient).map
        (fun (((a, _), wg'), ambient') => ((a, wg'), ambient')) =
      (o.run wg).run ambient := by
  exact congrFun (congrFun (h history) wg) ambient

section Generic
variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem erases_pure (a : α) : Erases (pure a : GhostT m α) (pure a) :=
  erasesT_pure a

theorem erases_lift (a : m α) : Erases (StateT.lift a : GhostT m α) a :=
  erasesT_lift a

theorem erases_liftM (a : m α) : Erases (liftM a : GhostT m α) a :=
  erasesT_liftM a

omit [LawfulMonad m] in
theorem erases_ite (p : Prop) [Decidable p]
    {gt ge : GhostT m α} {ot oe : m α}
    (ht : p → Erases gt ot) (he : ¬ p → Erases ge oe) :
    Erases (if p then gt else ge) (if p then ot else oe) :=
  erasesT_ite p ht he

theorem erases_bind {logged : GhostT m α} {original : m α}
    {lg : α → GhostT m β} {og : α → m β}
    (ha : Erases logged original) (hb : ∀ a, Erases (lg a) (og a)) :
    Erases (logged >>= lg) (original >>= og) :=
  erasesT_bind ha hb

theorem erases_bind_return {logged : GhostT m α} {original : m α}
    {lg : α → GhostT m α} (ha : Erases logged original)
    (hb : ∀ a, Erases (lg a) (pure a)) : Erases (logged >>= lg) original := by
  simpa only [bind_pure] using erases_bind ha hb

theorem erases_map {logged : GhostT m α} {original : m α}
    (f : α → β) (h : Erases logged original) :
    Erases (f <$> logged) (f <$> original) :=
  erasesT_map f h

theorem erases_forIn (xs : List α) (b : β)
    (logged : α → β → GhostT m (ForInStep β))
    (original : α → β → m (ForInStep β))
    (h : ∀ a b, Erases (logged a b) (original a b)) :
    Erases (forIn xs b logged) (forIn xs b original) :=
  erasesT_forIn xs b logged original h

theorem erases_range (r : Std.Legacy.Range) (b : β)
    (logged : Nat → β → GhostT m (ForInStep β))
    (original : Nat → β → m (ForInStep β))
    (h : ∀ a b, Erases (logged a b) (original a b)) :
    Erases (forIn r b logged) (forIn r b original) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact erases_forIn _ b logged original h

end Generic

def emit {m : Type → Type} [Monad m] (e : AcceptedEvent) : GhostT m Unit :=
  modifyThe History (· ++ [e])

theorem erases_emit {m : Type → Type} [Monad m] [LawfulMonad m] (e : AcceptedEvent) :
    Erases (emit e : GhostT m Unit) (pure ()) := by
  intro history
  change Prod.fst <$> (pure ((), history ++ [e]) : m (Unit × History)) = pure ()
  simp only [map_pure]

/-- Execute the actual validator once and record exactly its true results. -/
def counterLogged (kp : KeypairId) (nonce : Nat) : WGGhostM Bool := do
  let k ← StateT.lift (getKeypair kp)
  let ok ← StateT.lift (counterValidate kp nonce)
  if ok then emit ⟨k.internalId, nonce⟩
  return ok

/-- A getter before this getter-led function is redundant, including errors. -/
theorem getKeypair_before_validate (kp : KeypairId) (nonce : Nat) :
    (do let _ ← getKeypair kp; counterValidate kp nonce) = counterValidate kp nonce := by
  funext wg ambient
  change ((do let _ ← getKeypair kp; counterValidate kp nonce).run wg).run ambient =
    ((counterValidate kp nonce).run wg).run ambient
  cases hd : wg.dev with
  | none => simp [getKeypair, getDev, hd, counterValidate, invariant, AmbientM.invariant, StateT.run_bind, StateT.run_get] <;> rfl
  | some d =>
    cases hk : d.keypairs[kp]? with
    | none => simp [getKeypair, getDev, hd, hk, counterValidate, invariant, AmbientM.invariant, StateT.run_bind, StateT.run_get] <;> rfl
    | some k =>
      have hg := getKeypair_run wg ambient d kp k hd hk
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
    (wg wg' : WGWorld) (ambient ambient' : Ambient) (d : Device) (k : Keypair) (ok : Bool)
    (hd : wg.dev = some d) (hk : d.keypairs.get? kp = some k)
    (hr : ((counterValidate kp nonce).run wg).run ambient = .ok ((ok, wg'), ambient')) :
    (((counterLogged kp nonce).run history).run wg).run ambient =
      .ok (((ok, if ok then history ++ [⟨k.internalId, nonce⟩] else history), wg'), ambient') := by
  have hg := getKeypair_run wg ambient d kp k hd hk
  simp only [counterLogged, StateT.run_bind, StateT.run_lift, hg, hr,
    except_ok_bind, StateT.run_pure, except_pure]
  cases ok <;> rfl

/-- Lift the native observation through the mirror's actual product adapter.
The observer history is carried as the native action's return value. -/
def liftWGGhost (g : WGGhostM α) : GhostM α :=
  fun history => liftWG (g.run history)

/-- The lift retains the complete native outcome, including the exact Stop. -/
theorem liftWGGhost_run (g : WGGhostM α) (history : History) (world : World) :
    ((liftWGGhost g).run history).run world =
      (((g.run history).run world.wg).run world.ambient).map
        (fun (((a, history'), wg), ambient) => ((a, history'), { world with wg, ambient })) := by
  rfl

/-- Forgetting native observer history commutes with the actual product lift. -/
theorem erases_liftWGGhost {g : WGGhostM α} {o : WG.M α} (h : Erases g o) :
    Erases (liftWGGhost g) (liftWG o) := by
  intro history
  funext world
  have he := erases_runWG h history world.wg world.ambient
  change (((liftWGGhost g).run history).run world).map
      (fun ((a, _), w) => (a, w)) =
    ((o.run world.wg).run world.ambient).map
      (fun ((a, wg), ambient) => (a, { world with wg, ambient }))
  rw [liftWGGhost_run, ← he]
  cases (((g.run history).run world.wg).run world.ambient) <;> rfl

end Leanux.Proofs.Logged
