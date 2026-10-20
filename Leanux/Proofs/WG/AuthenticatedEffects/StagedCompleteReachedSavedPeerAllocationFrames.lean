import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSavedPeerFrames
import Leanux.Proofs.WG.Lifetimes.AllocationReleaseFrames

namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SavedPeer
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def AllocationResident (history : List LifetimeEvent) (pid : PeerId) (saved : Peer) (w : WGWorld) :=
  AllocationInv history w ∧ (Peers.snapshot w).slots pid = some saved.internalId

theorem allocation_write (pid : PeerId) (saved value : Peer) (history : List LifetimeEvent)
    (same : value.internalId = saved.internalId) :
    Preserves (AllocationResident history pid saved) (setPeer pid value) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before performed
  cases result
  have live : (Peers.snapshot w).slots pid = some value.internalId := by
    rw [same]
    exact before.2
  have identity := setPeer_identity pid value w v a b live performed
  have metadata := (ProjectedAction.iff_run_ambient _ _ _).mp
    (setPeer_metadata pid value) _ _ _ _ _ performed
  refine ⟨before.1.congr identity metadata, ?_⟩
  have peers : Peers.snapshot v = Peers.snapshot w := congrArg Prod.fst identity
  rw [peers]
  exact before.2

theorem Shape.allocation {α : Type} {body : WG.M α} (source : Shape pid saved body) (history : List LifetimeEvent) :
    Preserves (AllocationResident history pid saved) body := by
  induction source with
  | pure value => exact preserves_pure _
  | read => exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  | ambient body => exact hoare_liftAmbient _ _
  | write value same => exact allocation_write _ _ _ _ same.1
  | bind head tail ihHead ihTail => exact preserves_bind ihHead ihTail

theorem Point.allocation {α : Type} {body : WG.M α} {source : Shape pid saved body}
    (point : Point source w a v b)
    (before : AllocationResident history pid saved w) : AllocationResident history pid saved v := by
  revert before
  induction point with
  | entry source => intro before; exact before
  | returned source performed =>
      intro before
      exact (hoare_iff_run_ambient _ _ _).mp (source.allocation history) _ _ _ _ _ before performed
  | left tail point ih => exact ih
  | right head tail leading point ih =>
      intro before
      exact ih ((hoare_iff_run_ambient _ _ _).mp (head.allocation history) _ _ _ _ _ before leading)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SavedPeer
