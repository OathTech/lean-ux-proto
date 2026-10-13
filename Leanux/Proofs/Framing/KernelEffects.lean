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

end Leanux.Proofs.Framing
