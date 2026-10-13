import Leanux.Proofs.WG.Keypairs.OrdinaryHot
import Leanux.Proofs.Logged.Outer
import Leanux.Proofs.Logged.Tools

/-! Operational composition for the acceptance observer. The invariant is a
precondition, and each successful execution supplies an evolution witness.
This layer does not assume that the full observer caller chain is framed. -/
namespace Leanux.Proofs.WG.Keypairs
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def Evolves (g : GhostM α) : Prop :=
  ∀ h w x h' w', Inv (snapshot w) h →
    ((g.run h).run w) = .ok ((x, h'), w') →
    Evolution (snapshot w) h (snapshot w') h'

theorem Evolves.preserves {g : GhostM α} (hg : Evolves g)
    (h : History) (w : World) (x : α) (h' : History) (w' : World)
    (hi : Inv (snapshot w) h) (hr : ((g.run h).run w) = .ok ((x, h'), w')) :
    Inv (snapshot w') h' := (hg h w x h' w' hi hr).preserves hi

theorem evolves_pure (x : α) : Evolves (pure x) := by
  intro h w y h' w' hi hr
  cases hr
  exact .refl _ _

theorem evolves_throw (e : Stop) : Evolves (throw e : GhostM α) := by
  intro h w y h' w' hi hr
  cases hr

theorem evolves_lift {a : M α} (ha : OrdinaryAction a) : Evolves (StateT.lift a) := by
  intro h w x h' w' hi hr
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure] at hr
  cases he : a.run w with
  | error e => simp [he] at hr
  | ok out =>
    rcases out with ⟨x1, w1⟩
    simp only [he, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
    cases hr
    exact .ordinary (ha w _ _ he)

theorem evolves_liftM {a : M α} (ha : OrdinaryAction a) : Evolves (liftM a) :=
  evolves_lift ha

theorem counterLogged_evolution (kp : KeypairId) (nonce : Nat) : Evolves (counterLogged kp nonce) := by
  intro h w x h' w' hi hr
  exact counterLogged_evolves kp nonce w w' h h' x hi hr

theorem evolves_bind {g : GhostM α} {f : α → GhostM β}
    (hg : Evolves g) (hf : ∀ a, Evolves (f a)) : Evolves (g >>= f) := by
  intro h w x h' w' hi hr
  simp only [StateT.run_bind] at hr
  cases he : (g.run h).run w with
  | error e => simp [he] at hr
  | ok out =>
    rcases out with ⟨⟨a, h1⟩, w1⟩
    simp only [he, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
    have ev := hg h w a h1 w1 hi he
    exact .trans ev (hf a h1 w1 x h' w' (ev.preserves hi) hr)

theorem evolves_map (f : α → β) {g : GhostM α} (hg : Evolves g) : Evolves (f <$> g) := by
  simpa only [map_eq_pure_bind] using evolves_bind hg (fun x => evolves_pure (f x))

theorem evolves_discard {g : GhostM α} (hg : Evolves g) : Evolves (discard g) := by
  unfold Functor.discard
  exact evolves_map _ hg

theorem evolves_ite (p : Prop) [Decidable p] {gt ge : GhostM α}
    (ht : p → Evolves gt) (he : ¬p → Evolves ge) : Evolves (if p then gt else ge) := by
  by_cases hp : p
  · simpa only [if_pos hp] using ht hp
  · simpa only [if_neg hp] using he hp

theorem evolves_forIn (xs : List α) (b : β) (f : α → β → GhostM (ForInStep β))
    (hf : ∀ a b, Evolves (f a b)) : Evolves (forIn xs b f) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using evolves_pure b
  | cons a xs ih =>
    rw [List.forIn_cons]
    apply evolves_bind (hf a b)
    intro step
    cases step with
    | done b => exact evolves_pure b
    | yield b => exact ih b

theorem evolves_range (r : Std.Legacy.Range) (b : β)
    (f : Nat → β → GhostM (ForInStep β)) (hf : ∀ a b, Evolves (f a b)) :
    Evolves (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact evolves_forIn _ b f hf

theorem evolves_array (xs : Array α) (b : β) (f : α → β → GhostM (ForInStep β))
    (hf : ∀ a b, Evolves (f a b)) : Evolves (forIn xs b f) := by
  rw [← Array.forIn_toList]
  exact evolves_forIn _ b f hf

theorem evolves_getWorld : Evolves getWorld := by
  apply evolves_lift
  intro w x w' hr
  cases hr
  exact .refl _

theorem evolves_modifyWorld (f : World → World)
    (hf : ∀ w, Ordinary (snapshot w) (snapshot (f w))) : Evolves (modifyWorld f) := by
  apply evolves_lift
  intro w x w' hr
  cases hr
  exact hf w

/-- Retain the equality between a saved World and the state being replaced.
The observer's NAPI placement bookkeeping uses this adjacent read/write form. -/
theorem evolves_read_write (f : World → World) (next : World → GhostM α)
    (hf : ∀ w, Ordinary (snapshot w) (snapshot (f w)))
    (hn : ∀ w, Evolves (next w)) :
    Evolves (do let w ← getWorld; setWorld (f w); next w) := by
  intro h w x h' w' hi hr
  change ((next w).run h).run (f w) = .ok ((x, h'), w') at hr
  exact .trans (.ordinary (hf w))
    (hn w h (f w) x h' w' ((hf w).preserves hi) hr)

/-- A fixed starting point for verification conditions. Both the invariant
and the complete evolution witness are retained across each call. -/
def Track (s0 : Snapshot) (h0 h : History) (w : World) : Prop :=
  Inv (snapshot w) h ∧ Evolution s0 h0 (snapshot w) h

def GhostHoare (g : GhostM α) (P : History → World → Prop)
    (Q : α → History → World → Prop) : Prop :=
  ∀ h, Hoare (g.run h) (P h) (fun out w => Q out.1 out.2 w)

theorem ghostHoare_iff_triple (g : GhostM α) (P : History → World → Prop)
    (Q : α → History → World → Prop) :
    GhostHoare g P Q ↔
      ⦃fun h w => ⌜P h w⌝⦄ g ⦃⇓? x h w => ⌜Q x h w⌝⦄ := by
  constructor
  · intro hh h
    exact (hoare_iff_triple _ _ _).mp (hh h)
  · intro hh h
    exact (hoare_iff_triple _ _ _).mpr (hh h)

theorem Evolves.wp {g : GhostM α} (hg : Evolves g) (s0 : Snapshot) (h0 : History) :
    ⦃fun h w => ⌜Track s0 h0 h w⌝⦄ g
    ⦃⇓? _ h w => ⌜Track s0 h0 h w⌝⦄ := by
  apply (ghostHoare_iff_triple _ _ _).mp
  intro h w out w' hp hr
  have ev := hg h w out.1 out.2 w' hp.1 hr
  exact ⟨ev.preserves hp.1, .trans hp.2 ev⟩

theorem evolves_iff_wp (g : GhostM α) : Evolves g ↔
    ∀ s0 h0, ⦃fun h w => ⌜Track s0 h0 h w⌝⦄ g
      ⦃⇓? _ h w => ⌜Track s0 h0 h w⌝⦄ := by
  constructor
  · intro hg; exact hg.wp
  · intro hg h w x h' w' hi hr
    have hh := (ghostHoare_iff_triple _ _ _).mpr (hg (snapshot w) h)
    exact (hh h w (x, h') w' ⟨hi, .refl _ _⟩ hr).2

/-- The runner's explicit-world boundary merely rearranges the two states
and indexes errors; successful results have this exact correspondence. -/
theorem runAtLogged_ok_iff (index : Nat) (w : World) (g : GhostM α)
    (h : History) (x : α) (h' : History) (w' : World) :
    (runAtLogged index w g).run h = .ok ((x, w'), h') ↔
      ((g.run h).run w) = .ok ((x, h'), w') := by
  unfold runAtLogged
  cases he : ((g.run h).run w) with
  | error e =>
    simp only [StateT.run] at he
    simp [StateT.run, he, Except.map, Except.mapError]
  | ok out =>
    rcases out with ⟨⟨a, h1⟩, w1⟩
    simp only [StateT.run] at he
    simp [StateT.run, he, Except.map, Except.mapError, and_assoc, and_left_comm, and_comm]

theorem runAtLogged_tracks {g : GhostM α} (hg : Evolves g)
    (index : Nat) (w : World) (h : History) (x : α) (h' : History) (w' : World)
    (hp : Track s0 h0 h w)
    (hr : (runAtLogged index w g).run h = .ok ((x, w'), h')) : Track s0 h0 h' w' := by
  have ev := hg h w x h' w' hp.1 ((runAtLogged_ok_iff index w g h x h' w').mp hr)
  exact ⟨ev.preserves hp.1, .trans hp.2 ev⟩

/-- The outer runner has history state and indexed exceptions; its World is
an explicit return value rather than an implicit state layer. -/
def StateExceptHoare (a : StateT σ (Except ε) α) (P : σ → Prop) (Q : α → σ → Prop) : Prop :=
  ∀ s x s', P s → a.run s = .ok (x, s') → Q x s'

theorem stateExceptHoare_iff_triple (a : StateT σ (Except ε) α) (P : σ → Prop)
    (Q : α → σ → Prop) : StateExceptHoare a P Q ↔
      ⦃fun s => ⌜P s⌝⦄ a ⦃⇓? x s => ⌜Q x s⌝⦄ := by
  constructor
  · intro h s hp
    cases hr : a s with
    | error e => simp [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
        StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
        Pure.pure, ExceptConds.true, ExceptConds.const, hr]
    | ok out =>
      simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
        StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
        Pure.pure, ExceptConds.true, ExceptConds.const, hr] using h s out.1 out.2 hp hr
  · intro h s x s' hp hr
    have hh := h s hp
    change a s = .ok (x, s') at hr
    simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.true, ExceptConds.const, hr] using hh

theorem runAtLogged_wp {g : GhostM α} (hg : Evolves g) (s0 : Snapshot) (h0 : History)
    (index : Nat) (w : World) :
    ⦃fun h => ⌜Track s0 h0 h w⌝⦄ runAtLogged index w g
    ⦃⇓? out h => ⌜Track s0 h0 h out.2⌝⦄ := by
  apply (stateExceptHoare_iff_triple _ _ _).mp
  intro h out h' hp hr
  exact runAtLogged_tracks hg index w h out.1 h' out.2 hp hr

/-- Lift an ordinary mirror execution at an explicit World, as the runner
does for post-operation ambient record processing. -/
theorem ordinary_runAt_wp {a : M α} (ha : OrdinaryAction a) (s0 : Snapshot) (h0 : History)
    (index : Nat) (w : World) :
    ⦃fun h => ⌜Track s0 h0 h w⌝⦄
      (liftM ((a.run w).mapError (fun e => (index, e))) : StateT History (Except (Nat × Stop)) (α × World))
    ⦃⇓? out h => ⌜Track s0 h0 h out.2⌝⦄ := by
  apply (stateExceptHoare_iff_triple _ _ _).mp
  intro h out h' hp hr
  change ((a.run w).mapError (fun e => (index, e)) >>= fun x => pure (x, h)) = .ok (out, h') at hr
  cases he : a.run w with
  | error e =>
    simp [he, Except.mapError] at hr
    cases hr
  | ok value =>
    simp [he, Except.mapError] at hr
    rcases hr with ⟨rfl, rfl⟩
    have ho := ha w _ _ he
    exact ⟨ho.preserves hp.1, .trans hp.2 (.ordinary ho)⟩

end Leanux.Proofs.WG.Keypairs
