import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseContracts
import Leanux.Proofs.WG.Lifetimes.BatchItemSource

/-! The original selected clear worker and section wrapper with its native
final repayment exposed. Selection and hidden section records are unchanged. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def oneClearWith {m : Type → Type} [Monad m]
    (step : {α : Type} → Leanux.M α → m α)
    (worker : Worker → m Unit → m Unit) (clear : PeerId → m Unit) : m Unit := do
  let d ← step (liftWG getDev)
  let some headPid := d.clearWorkQueue.head? | step (invariant "no queued clear work")
  let pid ← match ← step (peekUnit .clearPeerWorker) with
    | some u => step (resolveUnit .clearPeerWorker u d.clearWorkQueue)
    | none => pure headPid
  step (liftWG (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}))
  worker .clearPeerWorker (clear pid)

theorem oneClear_native :
    oneClearWith (fun a => a) Env.runWorker (fun pid => liftWG (queuedExpiredZeroKeyMaterial pid)) =
      Env.runOneClearWorker := rfl

def oneClearObserved (release : HandshakeSecurity.StagedDisposal.Event → E)
    (decode : E → Option HandshakeSecurity.StagedDisposal.Event) : PrefixM E Unit :=
  oneClearWith liftPrefix runWorkerPrefix
    (fun pid => liftWGObserver (clearWith (observedOps release decode) pid))

theorem oneClear_erases {clear : PeerId → PrefixM E Unit}
    (hc : ∀ pid, ErasesPrefix (clear pid) (liftWG (queuedExpiredZeroKeyMaterial pid))) :
    ErasesPrefix (oneClearWith liftPrefix runWorkerPrefix clear) Env.runOneClearWorker := by
  rw [←oneClear_native]
  unfold oneClearWith
  repeat' first
    | with_reducible exact runWorkerPrefix_erases _ (hc _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | split
    | contradiction
    | (intro x; try dsimp only)

theorem oneClearObserved_erases (release : HandshakeSecurity.StagedDisposal.Event → E)
    (decode : E → Option HandshakeSecurity.StagedDisposal.Event) :
    ErasesPrefix (oneClearObserved release decode) Env.runOneClearWorker := by
  apply oneClear_erases
  intro pid
  apply liftWGObserver_erases
  simpa only [clear_native] using clear_erases (observedOps_erases release decode) pid

theorem oneClear_projects (ρ : E → Option F) {g : PeerId → PrefixM E Unit}
    {t : PeerId → PrefixM F Unit} (h : ∀ pid, ProjectsPrefix ρ id (g pid) (t pid)) :
    ProjectsPrefix ρ id (oneClearWith liftPrefix runWorkerPrefix g)
      (oneClearWith liftPrefix runWorkerPrefix t) := by
  unfold oneClearWith
  repeat' first
    | with_reducible exact Lifetimes.runWorkerPrefix_projects ρ _ (h _)
    | with_reducible exact projectsPrefix_lift ρ _
    | with_reducible exact projectsPrefix_pure ρ id _
    | with_reducible apply projectsPrefix_bind ρ id id
    | split
    | contradiction
    | rfl
    | (intro x; try dsimp only [id])

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
