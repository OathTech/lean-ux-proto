import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseWorker

/-! History frames for the actual clear-worker source, separate from native
source factoring. A quiet projection may hide the new disposal event only. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

private theorem lift_frame (ρ : E → Option F) (a : Leanux.M α) :
    HistoryFrame ρ (liftPrefix a) := by intro w h; rfl
private theorem pure_frame (ρ : E → Option F) (x : α) :
    HistoryFrame ρ (pure x : PrefixM E α) := by intro w h; rfl
private theorem choice_frame (ρ : E → Option F) (p : Prop) [Decidable p]
    (g t : PrefixM E α) (hg : HistoryFrame ρ g) (ht : HistoryFrame ρ t) :
    HistoryFrame ρ (if p then g else t) := by split <;> assumption

theorem worker_frame (ρ : E → Option F) (worker : Worker) {body : PrefixM E Unit}
    (hb : HistoryFrame ρ body) : HistoryFrame ρ (runWorkerPrefix worker body) := by
  unfold runWorkerPrefix
  repeat' first
    | exact hb
    | with_reducible exact lift_frame ρ _
    | with_reducible exact pure_frame ρ _
    | with_reducible apply HistoryFrame.bind
    | with_reducible apply choice_frame ρ
    | split
    | contradiction
    | (intro x; try dsimp only)

theorem oneClear_frame (ρ : E → Option F) {clear : PeerId → PrefixM E Unit}
    (hc : ∀ pid, HistoryFrame ρ (clear pid)) :
    HistoryFrame ρ (oneClearWith liftPrefix runWorkerPrefix clear) := by
  unfold oneClearWith
  repeat' first
    | with_reducible exact worker_frame ρ _ (hc _)
    | with_reducible exact lift_frame ρ _
    | with_reducible exact pure_frame ρ _
    | with_reducible apply HistoryFrame.bind
    | with_reducible apply choice_frame ρ
    | split
    | contradiction
    | (intro x; try dsimp only)

/-- The real worker selection and section wrapper preserve the native Stop and
old journal while exposing a final release before a later stopped suffix. -/
theorem oneClear_old (release : HandshakeSecurity.StagedDisposal.Event → E)
    (decode : E → Option HandshakeSecurity.StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none) :
    ProjectsPrefix ρ id (oneClearObserved release decode) (liftPrefix Env.runOneClearWorker) := by
  have erases := oneClearObserved_erases release decode
  have frames : HistoryFrame ρ (oneClearObserved release decode) :=
    oneClear_frame ρ (fun pid => StateHistoryFrame.liftWGObserver
      (clear_frame ρ (observedOps_frames release decode ρ quiet) pid))
  intro w h
  have native := erases w h
  have history := frames w h
  change (Env.runOneClearWorker.run w,h.filterMap ρ) = _
  rw [←native,history]
  cases (runPrefix (oneClearObserved release decode) w h).1 with
  | error err => rfl
  | ok out => rcases out with ⟨x,v⟩; rfl

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
