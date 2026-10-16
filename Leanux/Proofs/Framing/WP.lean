import Leanux.Proofs.Framing.Basic
import Leanux.Proofs.Framing.Allocation
import Leanux.Proofs.Framing.Index
import Leanux.Proofs.Framing.Lift

set_option pp.structureInstances false

namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing.Allocation

theorem branch_wp (d : Decision) (b : Bool) :
    ⦃fun (_ : Ambient) => ⌜True⌝⦄ AmbientM.branch d b ⦃⇓? x _ => ⌜x = b⌝⦄ := by
  mvcgen [AmbientM.branch]

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
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient a w' ambient' hp hr
  exact (hoare_iff_run_ambient _ _ _).mp
    (setKeypair_preserves query slot stamp counter k hp.2) w ambient a w' ambient' hp.1 hr

theorem keypairGet_preserves (kp : Option KeypairId) (slot stamp : Nat)
    (counter : ReplayCounter) :
    Preserves (Protected slot stamp counter) (keypairGet kp) := by
  unfold Preserves
  refine (hoare_iff_triple (keypairGet kp) _ _).mpr ?_
  mvcgen [keypairGet, getKeypair, getDev, setKeypair, modifyDev,
    branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, refcountIncNotZero,
    unsupported, invariant, AmbientM.unsupported, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [Protected]
  intro d k hd hk hid
  subst d
  simp only [Std.TreeMap.getElem?_insert] at hk
  split at hk <;> simp_all
  all_goals grind only

/-- Resolving an embedded peer word reads its owner without changing the
WireGuard state. This is not an access-coverage claim. -/
theorem indexOwner_peerWord_preserves (owner : IndexOwner) (P : WGWorld → Prop) :
    Preserves P owner.peerWord := by
  unfold Preserves Hoare
  cases owner
  all_goals mvcgen [IndexOwner.peerWord, getPeer, getKeypair, getDev,
    invariant, AmbientM.invariant]

theorem indexOwner_peerDeref_preserves (owner : IndexOwner) (P : WGWorld → Prop) :
    Preserves P owner.peerDeref := by
  have hw := indexOwner_peerWord_preserves owner P
  unfold Preserves Hoare at *
  mvcgen [IndexOwner.peerDeref, hw, unsupported, AmbientM.unsupported]

theorem keypairPut_preserves (kp : Option KeypairId) (now : Bool) (slot stamp : Nat)
    (counter : ReplayCounter) :
    Preserves (Protected slot stamp counter) (keypairPut kp now) := by
  unfold Preserves
  refine (hoare_iff_triple (keypairPut kp now) _ _).mpr ?_
  simp only [keypairPut, IndexOwner.peerDeref, IndexOwner.peerWord, indexRemove_eq]
  have hu : ∀ (a : IndexM Unit), Hoare (monadLift a : WG.M Unit) (Protected slot stamp counter)
      (fun _ => Protected slot stamp counter) := by
    intro a
    apply hoare_liftIndex
    intro g d table hp hd
    refine ⟨hp.1, ?_⟩
    intro d' k hd' hk hi
    cases hd'
    exact hp.2 d k hd hk hi
  unfold Hoare at hu
  have hg := fun query => getKeypair_wp query slot stamp counter
  have hs := fun query k => setKeypair_wp query slot stamp counter k
  mvcgen [hu, hg, hs, getDev, modifyDev,
    branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    refcountDecAndTest, unsupported, invariant, AmbientM.unsupported, AmbientM.invariant]
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
  have alloc_spec : Hoare (hiddenAlloc .kzallocKeypair : WG.M Bool)
      (Protected slot stamp counter) (fun _ => Protected slot stamp counter) :=
    hoare_liftAmbient (AmbientM.hiddenAlloc .kzallocKeypair) (Protected slot stamp counter)
  unfold Hoare at alloc_spec
  unfold Preserves
  refine (hoare_iff_triple (keypairCreate pid) _ _).mpr ?_
  mvcgen [keypairCreate, alloc_spec, getDev, setKeypair, modifyDev,
    branch, AmbientM.branch, invariant, AmbientM.invariant]
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
