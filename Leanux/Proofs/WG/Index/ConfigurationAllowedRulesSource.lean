import Leanux.Proofs.WG.Index.ConfigurationPeerModel
import Leanux.Proofs.WG.Config.BranchSource
import Leanux.Proofs.WG.Index.ConfigurationAllowedSource
import Leanux.Proofs.WG.Index.ConfigurationTailSource
import Leanux.Proofs.WG.Index.ConfigurationLoanSource
import Leanux.Proofs.WG.Index.ConfigurationEndpointFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

/-- The original native loop induction with result-indexed exit predicates. -/
theorem forIn_results {α : Type} (P Q : Int → WGWorld → Prop) (xs : List α) (ret : Int)
    (g : α → (Option Int × Int) → WG.M (ForInStep (Option Int × Int)))
    (step : ∀ x∈xs, ∀ ret, Hoare (g x (none,ret)) (P ret) (ResultExitStep P Q)) :
    Hoare (forIn xs (none,ret) g) (P ret) (ResultExitState P Q) := by
  induction xs generalizing ret with
  | nil =>
    rw [List.forIn_nil]
    exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderConfigTail.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigTail.pure_post)
      _ (fun _ h=>h)
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply hoare_bind _ _ (step x (by simp) ret)
    intro result
    cases result with
    | done acc =>
      exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderConfigTail.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigTail.pure_post)
        _ (fun _ h=>h)
    | yield acc =>
      rcases acc with ⟨early,ret⟩
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a result v b pre run
      have equal : early=none := pre.1
      subst early
      exact (hoare_iff_run_ambient _ _ _).mp
        (ih ret (fun y hy=>step y (by simp [hy]))) w a result v b pre.2 run

theorem forIn_exit {α : Type} (P Q : WGWorld → Prop) (xs : List α) (ret : Int)
    (g : α → (Option Int × Int) → WG.M (ForInStep (Option Int × Int)))
    (step : ∀ x∈xs, ∀ ret, Hoare (g x (none,ret)) P (ExitStep P Q)) :
    Hoare (forIn xs (none,ret) g) P (ExitState P Q) :=
  forIn_results (fun _=>P) (fun _=>Q) xs ret g step

/-- The actual malformed or negative path calls out; only a nonnegative yielding accumulator reaches next. -/
theorem allowedIps_results_rule (P : WGWorld → Prop) (Q : Int → WGWorld → Prop)
    (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (next : Int → WG.M Int)
    (allowed : ∀ ip, AllowedIpEntry.attrs ip ∈ attrs.allowedIps.getD [] →
      Preserves P (setAllowedip pid ip))
    (out : ∀ ret, ret<0 → Hoare (do
      peerPut peer
      _ ← branch .peerZeroPsk attrs.presharedKey.isSome
      pure ret : WG.M Int) P Q)
    (finish : ∀ ret, 0≤ret → Hoare (next ret) P Q) :
    Hoare (peerAllowedIpsSource attrs peer pid next) P Q := by
  have record (R : WGWorld → Prop) (site : Decision) (value : Bool) :
      Preserves R (branch site value : WG.M Bool) :=
    hoare_liftAmbient (AmbientM.branch site value) R
  unfold peerAllowedIpsSource peerAllowedIpsWith
  apply hoare_bind _ _ (record P _ _)
  intro has
  split
  · dsimp only
    change Hoare (_ >>= _) P _
    refine hoare_bind _ _ (hoare_consequence
      (forIn_results (fun ret w=>0≤ret ∧ P w) Q _ 0 _ ?_)
      (fun _ pre=>⟨Int.le_refl 0,pre⟩) (fun _ _ pre=>pre)) ?_
    · intro entry member ret
      dsimp only
      apply hoare_consequence ?_ (fun _ pre=>pre.2) (fun _ _ pre=>pre)
      apply hoare_bind _ _ (record P _ _)
      intro _
      cases entry with
      | malformed =>
        apply hoare_bind _ _ (record P _ _)
        intro _
        apply hoare_bind _ _ (out (-EINVAL) (by decide))
        intro result
        exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderConfigTail.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigTail.pure_post)
          _ (fun _ h=>h)
      | attrs ip =>
        apply hoare_bind _ _ (record P _ _)
        intro _
        apply hoare_bind _ _ (allowed ip member)
        intro result
        apply hoare_bind _ _ (Config.branch_state_spec P .peerAipErr (result<0))
        intro bad
        apply (hoare_iff_run_ambient _ _ _).mpr
        intro w a output v b pre run
        obtain ⟨rfl,pre⟩ := pre
        by_cases negative : result<0
        · have done : Hoare (do
              let result' ← (do peerPut peer; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure result : WG.M Int)
              pure (.done (some result',result)) : WG.M (ForInStep (Option Int×Int)))
              P (ResultExitStep (fun ret w=>0≤ret ∧ P w) Q) :=
            hoare_bind _ _ (out result negative) (fun result'=>
            (pinned_const _private.Leanux.Proofs.WG.Queues.HolderConfigTail.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigTail.pure_post)
              (ForInStep.done (some result',result)) (fun _ h=>h))
          exact (hoare_iff_run_ambient _ _ _).mp done w a output v b pre
            (by simpa only [negative,decide_true,ite_true,monadLift_self] using run)
        · have done : Hoare (pure (.yield (none,result)) : WG.M (ForInStep (Option Int×Int)))
              P (ResultExitStep (fun ret w=>0≤ret ∧ P w) Q) :=
            (pinned_const _private.Leanux.Proofs.WG.Queues.HolderConfigTail.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigTail.pure_post)
              _ (fun _ h=>⟨rfl,by omega,h⟩)
          exact (hoare_iff_run_ambient _ _ _).mp done w a output v b pre
            (by simpa only [negative,decide_false,Bool.false_eq_true,ite_false] using run)
    · intro acc
      rcases acc with ⟨early,ret⟩
      cases early with
      | some result =>
        exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderConfigTail.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigTail.pure_post)
          _ (fun _ h=>h)
      | none =>
        apply hoare_bind _ _ (record _ _ _)
        intro _
        apply (hoare_iff_run_ambient _ _ _).mpr
        intro w a result v b pre run
        exact (hoare_iff_run_ambient _ _ _).mp (finish ret pre.1) w a result v b pre.2 run
  · exact finish 0 (Int.le_refl 0)

theorem allowedIps_members_rule (P Q : WGWorld → Prop) (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) (next : Int → WG.M Int)
    (allowed : ∀ ip, AllowedIpEntry.attrs ip ∈ attrs.allowedIps.getD [] → Preserves P (setAllowedip pid ip))
    (out : ∀ ret, Hoare (do
      peerPut peer
      _ ← branch .peerZeroPsk attrs.presharedKey.isSome
      pure ret : WG.M Int) P (fun _=>Q))
    (finish : ∀ ret, Hoare (next ret) P (fun _=>Q)) :
    Hoare (peerAllowedIpsSource attrs peer pid next) P (fun _=>Q) :=
  allowedIps_results_rule P (fun _=>Q) attrs peer pid next allowed
    (fun ret _=>out ret) (fun ret _=>finish ret)

end Leanux.Proofs.WG.Index.ConfigurationIndex
