import Leanux.Proofs.WG.Index.ConfigurationPeerModel
import Leanux.Proofs.WG.Index.ConfigurationAllowedSource
import Leanux.Proofs.WG.Index.ConfigurationTailSource
import Leanux.Proofs.WG.Index.ConfigurationLoanSource
import Leanux.Proofs.WG.Index.ConfigurationEndpointFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

/-- Source-control composition retained unchanged from the owned peer rule. -/
theorem forIn_exit {α : Type} (P Q : WGWorld → Prop) (xs : List α) (ret : Int)
    (g : α → (Option Int × Int) → WG.M (ForInStep (Option Int × Int)))
    (step : ∀ x∈xs, ∀ ret, Hoare (g x (none,ret)) P (ExitStep P Q)) :
    Hoare (forIn xs (none,ret) g) P (ExitState P Q) := by
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

theorem allowedIps_members_rule (P Q : WGWorld → Prop) (attrs : PeerAttrs)
    (peer : Option PeerId) (pid : PeerId) (next : Int → WG.M Int)
    (allowed : ∀ ip, AllowedIpEntry.attrs ip ∈ attrs.allowedIps.getD [] → Preserves P (setAllowedip pid ip))
    (out : ∀ ret, Hoare (do
      peerPut peer
      _ ← branch .peerZeroPsk attrs.presharedKey.isSome
      pure ret : WG.M Int) P (fun _=>Q))
    (finish : ∀ ret, Hoare (next ret) P (fun _=>Q)) :
    Hoare (peerAllowedIpsSource attrs peer pid next) P (fun _=>Q) := by
  have record (site : Decision) (value : Bool) : Preserves P (branch site value : WG.M Bool) :=
    hoare_liftAmbient (AmbientM.branch site value) P
  unfold peerAllowedIpsSource peerAllowedIpsWith
  apply hoare_bind _ _ (record _ _)
  intro has
  split
  · dsimp only
    change Hoare (_ >>= _) P _
    refine hoare_bind _ _ (forIn_exit P Q _ _ _ ?_) ?_
    · intro entry member ret
      dsimp only
      apply hoare_bind _ _ (record _ _)
      intro _
      cases entry with
      | malformed =>
        apply hoare_bind _ _ (record _ _)
        intro _
        apply hoare_bind _ _ (out (-EINVAL))
        intro result
        exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderConfigTail.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigTail.pure_post)
          _ (fun _ h=>h)
      | attrs ip =>
        apply hoare_bind _ _ (record _ _)
        intro _
        apply hoare_bind _ _ (allowed ip member)
        intro result
        apply hoare_bind _ _ (record _ _)
        intro bad
        split
        · apply hoare_bind _ _ (out result)
          intro result'
          exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderConfigTail.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigTail.pure_post)
            _ (fun _ h=>h)
        · exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderConfigTail.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigTail.pure_post)
            _ (fun _ h=>⟨rfl,h⟩)
    · intro acc
      rcases acc with ⟨early,ret⟩
      cases early with
      | some result =>
        exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderConfigTail.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderConfigTail.pure_post)
          _ (fun _ h=>h)
      | none =>
        apply hoare_bind _ _ (record _ _)
        intro _
        exact finish ret
  · exact finish 0

end Leanux.Proofs.WG.Index.ConfigurationIndex
