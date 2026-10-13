import Leanux.Proofs.Framing.WP

/-! Kernel-preserving original record consumers and refcount helpers. These
contracts are shared by all projection frames, without a legacy keypair frame dependency. -/
namespace Leanux.Proofs.Framing
open Leanux Std.Do Leanux.Proofs.Framing.Allocation

/-- The same decreasing encounter count applies at every allocation site. -/
theorem hiddenAlloc_sameKernel (site : AllocSite) : SameKernel (hiddenAlloc site) := by
  apply sameKernel_of_wp
  intro k
  rw [← allocationOutcome_eq]
  mvcgen [allocationOutcome, recordOutcome, placeholderOutcome, hidden, skipAmbient, invariant, unsupported]
  invariants
  | inv1 _ n _ _ _ _ _ _ => fun r _ => ⟨n - r.2 + 1⟩
  | inv2 => ((⇓? _ w => ⌜w.k = k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try (letI : Nonempty World := ⟨by assumption⟩; infer_instance)
  all_goals try simp_all [WhileVariant.eval, SVal.evalsTo, SVal.uncurry]
  all_goals omega

theorem hiddenClock_sameKernel (site : HiddenSite) : SameKernel (hiddenClock site) := by
  apply sameKernel_of_wp
  intro k
  have hs := sameKernel_wp _ (hidden_sameKernel site) (fun k' => k' = k)
  mvcgen [hiddenClock, hs]

theorem refcountDecAndTest_sameKernel (old : Nat) : SameKernel (refcountDecAndTest old) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [refcountDecAndTest, branchCmp, branchCmpExcluded, branch, unsupported]

theorem refcountInc_sameKernel (old : Nat) : SameKernel (refcountInc old) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [refcountInc, branchCmp, branchCmpExcluded, branch, unsupported]

theorem refcountIncGuestWide_sameKernel (x : OperandExclusion) : SameKernel (refcountIncGuestWide x) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [refcountIncGuestWide, branchCmp, branchCmpExcluded, branch, unsupported]

theorem refcountIncNotZero_sameKernel (old : Nat) : SameKernel (refcountIncNotZero old) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [refcountIncNotZero, branchCmp, branchCmpExcluded, branch, unsupported]


theorem routeLookup_sameKernel (family src dst : Nat) : SameKernel (routeLookup family src dst) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [routeLookup]

theorem peekHiddenSite_sameKernel : SameKernel peekHiddenSite := by
  apply sameKernel_of_wp
  intro k
  have hs := sameKernel_wp _ skipAmbient_sameKernel (fun s => s = k)
  mvcgen [peekHiddenSite, hs]

theorem skipCutSites_sameKernel (sites : List HiddenSite) : SameKernel (skipCutSites sites) := by
  apply sameKernel_of_wp
  intro k
  have hs := sameKernel_wp _ skipAmbient_sameKernel (fun s => s = k)
  mvcgen [skipCutSites, hs, unsupported, invariant]
  all_goals try exact ((⇓? _ w => ⌜w.k = k⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  all_goals trivial

theorem skipCut_sameKernel (sites : List HiddenSite) : SameKernel (skipCut sites) := by
  apply sameKernel_of_wp
  intro k
  have hs := sameKernel_wp _ (skipCutSites_sameKernel sites) (fun s => s = k)
  unfold skipCut
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  exact sameKernel_wp _ (sameKernel_bind (skipCutSites_sameKernel sites) (fun _ => sameKernel_pure ())) (fun s => s = k)

end Leanux.Proofs.Framing
