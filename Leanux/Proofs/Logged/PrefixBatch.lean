import Leanux.Proofs.Logged.PrefixWorkers
import Leanux.Proofs.Framing.Batch

/-! Section wrappers shared by failure-retaining observations. -/
namespace Leanux.Proofs.Logged
open Leanux Leanux.Proofs.Framing

theorem kernelLiftPrefix_preserves (hs : ∀ h w, I h w → S h)
    (hk : ∀ h w v, v.k = w.k → I h w → I h v) (ha : SameKernel a) :
    PrefixPreserves I S (liftPrefix a) :=
  PrefixEnsures.preserves (PrefixEnsures.lift a hs (fun h w x v hi hr => hk h w v (ha w x v hr) hi))

/-- Insert an observed pure computation without adding an original action. -/
theorem erasesPrefix_bind_pure (hg : ErasesPrefix g (pure x))
    (hf : ErasesPrefix (f x) a) : ErasesPrefix (g >>= f) a := by
  intro w h
  have he := hg w h
  cases hr : runPrefix g w h with
  | mk result hist =>
    rw [hr] at he
    cases result with
    | error e => cases he
    | ok out =>
      change Except.ok out = Except.ok (x, w) at he
      cases he
      simpa only [runPrefix_bind, hr] using hf w hist

def runWorkerPrefix (worker : Worker) (body : PrefixM Event Unit) : PrefixM Event Unit := do
  _ ← liftPrefix (hidden (.sectionStart worker))
  if worker == .netRx then
    liftPrefix (modify fun s => {s with netRxSections := s.netRxSections + 1, netRxSection := s.netRxSections + 1})
  body
  if worker == .netRx then liftPrefix (modify fun s => {s with netRxSection := 0})
  _ ← liftPrefix (hidden (.sectionStop worker))

theorem runWorkerPrefix_erases (worker : Worker) (hb : ErasesPrefix body originalBody) :
    ErasesPrefix (runWorkerPrefix worker body) (Env.runWorker worker originalBody) := by
  unfold runWorkerPrefix Env.runWorker
  repeat' first
    | exact hb
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | split
    | (intro x; try dsimp only)

theorem runWorkerPrefix_preserves (hs : ∀ h w, I h w → S h)
    (hk : ∀ h w v, v.k = w.k → I h w → I h v) (worker : Worker)
    (hb : PrefixPreserves I S body) :
    PrefixPreserves I S (runWorkerPrefix worker body) := by
  unfold runWorkerPrefix
  repeat' first
    | exact hb
    | exact kernelLiftPrefix_preserves hs hk (hidden_sameKernel _)
    | exact kernelLiftPrefix_preserves hs hk (by intro w x v hr; cases hr; rfl)
    | exact PrefixPreserves.pure hs _
    | apply PrefixPreserves.bind
    | split
    | (intro x; try dsimp only)


end Leanux.Proofs.Logged
