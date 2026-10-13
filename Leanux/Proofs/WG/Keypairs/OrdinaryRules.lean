import Leanux.Proofs.WG.Keypairs.Frames.Tools
import Leanux.Proofs.Logged.RxPoll

/-! Direct composition for callers whose individual actions already frame
the lifetime store. Saved keypair replacements use the stronger WP contracts
in the helper proofs, rather than an unconditional rule for replacement. -/
namespace Leanux.Proofs.WG.Keypairs
open Leanux Leanux.WG Std.Do

theorem ordinary_throw (e : Stop) : OrdinaryAction (throw e : M α) := by
  intro w x w' hr
  cases hr

theorem ordinary_map (f : α → β) {a : M α} (ha : OrdinaryAction a) :
    OrdinaryAction (f <$> a) := by
  simpa only [map_eq_pure_bind] using ordinary_bind ha (fun x => ordinary_pure (f x))

theorem ordinary_discard {a : M α} (ha : OrdinaryAction a) : OrdinaryAction (discard a) := by
  unfold Functor.discard
  exact ordinary_map _ ha

theorem ordinary_ite (p : Prop) [Decidable p] {a b : M α}
    (ha : p → OrdinaryAction a) (hb : ¬p → OrdinaryAction b) :
    OrdinaryAction (if p then a else b) := by
  by_cases hp : p
  · simpa only [if_pos hp] using ha hp
  · simpa only [if_neg hp] using hb hp

theorem ordinary_forIn (xs : List α) (b : β) (f : α → β → M (ForInStep β))
    (hf : ∀ a b, OrdinaryAction (f a b)) : OrdinaryAction (forIn xs b f) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using ordinary_pure b
  | cons a xs ih =>
    rw [List.forIn_cons]
    apply ordinary_bind (hf a b)
    intro step
    cases step with
    | done b => exact ordinary_pure b
    | yield b => exact ih b

theorem ordinary_range (r : Std.Legacy.Range) (b : β)
    (f : Nat → β → M (ForInStep β)) (hf : ∀ a b, OrdinaryAction (f a b)) :
    OrdinaryAction (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact ordinary_forIn _ b f hf

theorem ordinary_forM (xs : List α) (f : α → M PUnit)
    (hf : ∀ a, OrdinaryAction (f a)) : OrdinaryAction (xs.forM f) := by
  induction xs with
  | nil => simpa only [List.forM_eq_forM, List.forM_nil] using ordinary_pure PUnit.unit
  | cons a xs ih =>
    simpa only [List.forM_eq_forM, List.forM_cons] using ordinary_bind (hf a) (fun _ => ih)

theorem ordinary_array (xs : Array α) (b : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, OrdinaryAction (f a b)) :
    OrdinaryAction (forIn xs b f) := by
  rw [← Array.forIn_toList]
  exact ordinary_forIn _ b f hf

theorem ordinary_get : OrdinaryAction (get : M World) := by
  intro w x w' hr
  cases hr
  exact .refl _

theorem ordinary_modify (f : World → World)
    (hf : ∀ w, Ordinary (snapshot w) (snapshot (f w))) : OrdinaryAction (modify f) := by
  intro w x w' hr
  cases hr
  exact hf w

theorem ordinary_modifyDev (f : Device → Device)
    (hf : ∀ d, (f d).keypairs = d.keypairs) : OrdinaryAction (modifyDev f) := by
  apply SameSnapshot.ordinary
  apply sameSnapshot_of_wp
  intro s
  exact modifyDev_snapshot_spec (fun t => t = s) f hf

theorem ordinary_andM (a b : M Bool) (ha : OrdinaryAction a) (hb : OrdinaryAction b) :
    OrdinaryAction (Leanux.WG.andM a b) := by
  unfold Leanux.WG.andM
  apply ordinary_bind ha
  intro result
  cases result
  · exact ordinary_pure false
  · exact hb

theorem ordinary_orM (a b : M Bool) (ha : OrdinaryAction a) (hb : OrdinaryAction b) :
    OrdinaryAction (Leanux.WG.orM a b) := by
  unfold Leanux.WG.orM
  apply ordinary_bind ha
  intro result
  cases result
  · exact hb
  · exact ordinary_pure true

/-- Inspect the action head without evaluating the action or its framing predicate. -/
elab "ordinary_head " n:ident : tactic => do
  let t := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  unless t.isAppOf ``OrdinaryAction do
    Lean.throwError "expected an OrdinaryAction goal"
  let a := t.getAppArgs.back! |>.consumeMData |>.headBeta
  let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  unless a.isAppOf name do
    Lean.throwError "different action head: {a.getAppFn} versus {name}"

macro "ordinary_step" : tactic => `(tactic|
  first
    | contradiction
    | intro_forall
    | with_reducible assumption
    | (ordinary_head Pure.pure; exact ordinary_pure _)
    | (ordinary_head MonadExceptOf.throw; exact ordinary_throw _)
    | (ordinary_head get; exact ordinary_get)
    | (ordinary_head modify; refine ordinary_modify _ ?_; intro w; exact Ordinary.refl _)
    | (ordinary_head Leanux.WG.modifyDev; refine ordinary_modifyDev _ ?_; intro d; rfl)
    | (ordinary_head Leanux.WG.andM; refine ordinary_andM _ _ ?_ ?_)
    | (ordinary_head Leanux.WG.orM; refine ordinary_orM _ _ ?_ ?_)
    | (ordinary_head ite; refine ordinary_ite _ ?_ ?_)
    | (ordinary_head Bind.bind; refine ordinary_bind ?_ ?_)
    | (ordinary_head Functor.discard; refine ordinary_discard ?_)
    | (ordinary_head Functor.map; refine ordinary_map _ ?_)
    | (ordinary_head ForIn.forIn; with_reducible refine ordinary_range _ _ _ ?_)
    | (ordinary_head ForIn.forIn; with_reducible refine ordinary_forIn _ _ _ ?_)
    | (ordinary_head List.forM; with_reducible refine ordinary_forM _ _ ?_)
    | (ordinary_head ForM.forM; with_reducible refine ordinary_forM _ _ ?_)
    | (ordinary_head ForIn.forIn; with_reducible refine ordinary_array _ _ _ ?_)
    | dsimp only
    | (split <;> try simp_all only [Option.some.injEq, List.cons.injEq,
        Prod.mk.injEq, reduceCtorEq, forall_eq', not_true_eq_false]))

end Leanux.Proofs.WG.Keypairs
