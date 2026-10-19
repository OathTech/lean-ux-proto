import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPrimitiveFrames

/-! All cuts of the literal repayment tree preserve the same selected
ledger, cached peer and native take anchor. This includes a decrement or
index erasure followed by a later native failure. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations
set_option maxHeartbeats 600000

theorem KeyPoint.selected {action : WG.M α} {shape : KeyShape action}
    (point : KeyPoint shape w a leaf v b rest)
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a) :
    CompleteSelected.Ready ledger debts locals generation pid peer position h v b := by
  induction point with
  | entry=>exact before
  | returned shape run=>exact shape.selected before run
  | left tail point ih=>exact ih before
  | right head tail leading point ih=>exact ih (head.selected before leading)

theorem repayment_every_point
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a)
    (point : KeyPoint (keyShape kid) w a leaf v b rest) :
    CompleteSelected.Ready ledger debts locals generation pid peer position h v b ∧
      runWGPrefix (liftWGPrefix (keypairPut kid false) : WGPrefix Event Unit) w a h=
        runWGPrefix (liftWGPrefix rest) v b h := by
  refine ⟨point.selected before,?_⟩
  simp only [runWGPrefix_lift,point.residual]

theorem repayment_stopped_point
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a)
    (point : KeyPoint (keyShape kid) w a leaf v b rest)
    (failed : (rest.run v).run b=.error reason) :
    CompleteSelected.Ready ledger debts locals generation pid peer position h v b ∧
      runWGPrefix (liftWGPrefix (keypairPut kid false) : WGPrefix Event Unit) w a h=(.error reason,h) :=
  ⟨point.selected before,by rw [runWGPrefix_lift,point.stopped failed]⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPrimitive
