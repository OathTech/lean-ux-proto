import Leanux.Proofs.Framing.Basic
import Leanux.Proofs.Framing.Allocation
import Leanux.Proofs.Framing.Index
import Std.Tactic.Do

set_option pp.structureInstances false

namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing.Allocation

/-- The bundled `Spec.throw_Except` has unused monad/universe parameters.
This equivalent local rule fixes those unconstrained elaboration variables. -/
@[spec high] theorem except_throw_wp {ε α : Type} (e : ε)
    (Q : PostCond α (.except ε .pure)) :
    Triple (ps := .except ε .pure) (MonadExceptOf.throw e : Except ε α) (spred(Q.2.1 e)) Q := by
  simp [Triple.iff]

theorem hoare_iff_triple (a : M α) (P : World → Prop) (Q : α → World → Prop) :
    Hoare a P Q ↔ ⦃fun w => ⌜P w⌝⦄ a ⦃⇓? x w => ⌜Q x w⌝⦄ := by
  constructor
  · intro h w hp
    cases hr : a w with
    | error e => simp [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply, StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure, Pure.pure, ExceptConds.true, ExceptConds.const, hr]
    | ok out =>
      simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply, StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure, Pure.pure, ExceptConds.true, ExceptConds.const, hr] using
        h w out.1 out.2 hp hr
  · intro h w x w' hp hr
    have hh := h w hp
    change a w = .ok (x, w') at hr
    simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply, StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure, Pure.pure, ExceptConds.true, ExceptConds.const, hr] using hh

/-- A total weakest-precondition triple is equivalent to normal execution
with its stated postcondition in this StateT/Except mirror. -/
theorem total_iff_run (a : M α) (P : World → Prop) (Q : α → World → Prop) :
    (⦃fun w => ⌜P w⌝⦄ a ⦃⇓ x w => ⌜Q x w⌝⦄) ↔
      ∀ w, P w → ∃ x w', a.run w = .ok (x, w') ∧ Q x w' := by
  constructor
  · intro h w hp
    have hh := h w hp
    cases hr : a w with
    | error e =>
      simp [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
        StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
        Pure.pure, ExceptConds.false, ExceptConds.const, hr] at hh
    | ok out =>
      refine ⟨out.1, out.2, hr, ?_⟩
      simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
        StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
        Pure.pure, ExceptConds.false, ExceptConds.const, hr] using hh
  · intro h w hp
    rcases h w hp with ⟨x, w', hr, hq⟩
    change a w = .ok (x, w') at hr
    simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
      StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
      Pure.pure, ExceptConds.false, ExceptConds.const, hr] using hq

theorem branch_wp (d : Decision) (b : Bool) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ branch d b ⦃⇓? x w => ⌜x = b ∧ P w.k⌝⦄ := by
  unfold branch
  mvcgen

theorem getKeypair_wp (query slot stamp : Nat) (counter : ReplayCounter) :
    ⦃fun w => ⌜Protected slot stamp counter w⌝⦄ getKeypair query
    ⦃⇓? k w => ⌜Protected slot stamp counter w ∧
      (query = slot → k.internalId = stamp → k.receivingCounter = counter)⌝⦄ :=
  (hoare_iff_triple _ _ _).mp (getKeypair_spec query slot stamp counter)

theorem setKeypair_wp (query slot stamp : Nat) (counter : ReplayCounter) (k : Keypair) :
    ⦃fun w => ⌜Protected slot stamp counter w ∧
      (query = slot → k.internalId = stamp → k.receivingCounter = counter)⌝⦄
    setKeypair query k ⦃⇓? _ w => ⌜Protected slot stamp counter w⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w a w' hp hr
  exact setKeypair_preserves query slot stamp counter k hp.2 w a w' hp.1 hr

theorem sameKernel_of_wp (a : M α)
    (h : ∀ k, ⦃fun w => ⌜w.k = k⌝⦄ a ⦃⇓? _ w => ⌜w.k = k⌝⦄) : SameKernel a := by
  intro w x w' hr
  exact (hoare_iff_triple _ _ _).mpr (h w.k) w x w' rfl hr

theorem sameKernel_wp (a : M α) (h : SameKernel a) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ a ⦃⇓? _ w => ⌜P w.k⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x w' hp hr
  simpa only [h w x w' hr] using hp

theorem skipAmbient_sameKernel : SameKernel skipAmbient := by
  apply sameKernel_of_wp
  intro k
  mvcgen [skipAmbient]

theorem noteNetRxStart_sameKernel (site : Nat) : SameKernel (noteNetRxStart site) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [noteNetRxStart]

theorem hidden_sameKernel (s : HiddenSite) : SameKernel (hidden s) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [hidden, skipAmbient, noteNetRxStart]

theorem allocRecord_sameKernel (s : AllocSite) : SameKernel (recordOutcome s) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [recordOutcome, hidden, skipAmbient, noteNetRxStart]

theorem allocPlaceholder_sameKernel (s : AllocSite) : SameKernel (placeholderOutcome s) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [placeholderOutcome, unsupported]

theorem keypairAllocation_sameKernel : SameKernel (hiddenAlloc .kzallocKeypair) := by
  apply sameKernel_of_wp
  intro k
  rw [← allocationOutcome_eq]
  mvcgen [allocationOutcome, recordOutcome, placeholderOutcome, hidden, skipAmbient, noteNetRxStart, invariant, unsupported]
  invariants
  | inv1 _ n _ _ _ _ _ _ => fun r _ => ⟨n - r.2 + 1⟩
  | inv2 => ((⇓? _ w => ⌜w.k = k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (letI : Nonempty World := ⟨by assumption⟩; infer_instance)
  all_goals try simp_all [WhileVariant.eval, SVal.evalsTo, SVal.uncurry]
  all_goals omega

theorem keypairGet_preserves (kp : Option KeypairId) (slot stamp : Nat)
    (counter : ReplayCounter) :
    Preserves (Protected slot stamp counter) (keypairGet kp) := by
  unfold Preserves
  refine (hoare_iff_triple (keypairGet kp) _ _).mpr ?_
  mvcgen [keypairGet, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    branch, branchCmp, refcountIncNotZero, unsupported, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [Protected]
  intro d k hd hk hid
  subst d
  simp only [Std.TreeMap.getElem?_insert] at hk
  split at hk <;> simp_all
  all_goals grind only

theorem indexUnhash_protected (d : Decision) (hashed : IndexEntry → Bool)
    (slot stamp : Nat) (counter : ReplayCounter) :
    ⦃fun w => ⌜Protected slot stamp counter w⌝⦄ indexUnhash d hashed
    ⦃⇓? _ w => ⌜Protected slot stamp counter w⌝⦄ := by
  mvcgen [indexUnhash, getDev, getK, branch, modifyDev, modifyK, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [Protected]
  intro d k hd hk hi
  subst d
  grind only

/-- Resolving an embedded peer word reads its owner and does not mutate the
Kernel. This frame is not an access-coverage claim. -/
theorem indexOwner_peerWord_sameKernel (owner : IndexOwner) : SameKernel owner.peerWord := by
  cases owner <;> apply sameKernel_of_wp <;> intro k
  all_goals mvcgen [IndexOwner.peerWord, getPeer, getKeypair, getDev, getK, invariant]

theorem indexOwner_peerDeref_sameKernel (owner : IndexOwner) : SameKernel owner.peerDeref := by
  apply sameKernel_of_wp
  intro k
  have hw := sameKernel_wp _ (indexOwner_peerWord_sameKernel owner) (fun s => s = k)
  mvcgen [IndexOwner.peerDeref, hw, unsupported]

theorem keypairPut_preserves (kp : Option KeypairId) (now : Bool) (slot stamp : Nat)
    (counter : ReplayCounter) :
    Preserves (Protected slot stamp counter) (keypairPut kp now) := by
  unfold Preserves
  refine (hoare_iff_triple (keypairPut kp now) _ _).mpr ?_
  simp only [keypairPut, IndexOwner.peerDeref, IndexOwner.peerWord, indexRemove_eq]
  have hu := fun d hashed => indexUnhash_protected d hashed slot stamp counter
  have hg := fun query => getKeypair_wp query slot stamp counter
  have hs := fun query k => setKeypair_wp query slot stamp counter k
  mvcgen [hu, hg, hs, getDev, getK, modifyDev, modifyK,
    branch, branchCmp, refcountDecAndTest, unsupported, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [Protected]
  all_goals try assumption
  all_goals
    intro d k x hx hd hk hi
    subst d
    simp only [Std.TreeMap.getElem?_erase] at hk
    split at hk <;> simp_all

theorem keypairCreate_preserves (pid : Option PeerId) (slot stamp : Nat)
    (counter : ReplayCounter) :
    Preserves (Protected slot stamp counter) (keypairCreate pid) := by
  have alloc_spec := sameKernel_wp _ keypairAllocation_sameKernel
    (fun k => stamp ≤ k.keypairCounter ∧
      ∀ d v, k.wg = some d → d.keypairs[slot]? = some v →
        v.internalId = stamp → v.receivingCounter = counter)
  unfold Preserves
  refine (hoare_iff_triple (keypairCreate pid) _ _).mpr ?_
  mvcgen [keypairCreate, alloc_spec, getDev, getK, setKeypair, modifyDev, modifyK,
    branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [Protected]
  all_goals
    constructor
    · omega
    · intro d k hd hk hid
      subst d
      simp only [Std.TreeMap.getElem?_insert] at hk
      split at hk <;> simp_all
      all_goals grind only

end Leanux.Proofs.Framing
