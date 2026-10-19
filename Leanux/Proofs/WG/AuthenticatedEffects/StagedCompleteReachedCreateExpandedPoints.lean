import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreateMutationPoints
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreateCleanupPoints
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreateCompositionRelease

/-! One creation source family joins the canonical tree, key and peer
repayments, silent mutations and refused-cleanup intervals. Evidence retains
the particular original ledger and distinguishes pending disposal records.
This does not assert coverage of every initialized caller or finer atom. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateExpanded
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open AllocatedObligation CompleteCarrier

inductive Point (pid : PeerId) (items : List SkbId) (w : World) (h : List Event) :
    World → List Event → Prop where
  | canonical (point : CreateComposition.Point pid items w h v last) : Point pid items w h v last
  | mutation (point : CreateMutation.Point pid items w h v last) : Point pid items w h v last
  | cleanup (point : CreateCleanup.Point pid items w h v last) : Point pid items w h v last
  | release (point : CreateComposition.ReleasePoint pid items w h v last) : Point pid items w h v last

inductive Evidence (rootLedger : Staged.Obligations.Ledger) (debts : List CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (pid : PeerId) (items : List SkbId) :
    List Event → World → Prop where
  | phase (evidence : CreatePhase.Evidence rootLedger debts locals pid items h w) :
      Evidence rootLedger debts locals pid items h w
  | release (current : Staged.Obligations.Ledger) (active : List RetirementSecurity.TxLocalBatch)
      (steps : Staged.Obligations.Step rootLedger current)
      (evidence : NestedPeer.Evidence current debts active h w) : Evidence rootLedger debts locals pid items h w

/-- Every declared creation cut preserves ownership or its actual pending
disposal receipt on the same original allocation lineage. -/
theorem Point.evidence (point : Point pid items w h v last)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (pending : CreateDisposal.PendingBatch h ledger items) : Evidence ledger debts locals pid items last v := by
  cases point with
  | canonical point=>exact .phase (.live (point.live pending before))
  | mutation point=>exact .phase (.live (point.live before pending))
  | cleanup point=>exact .phase (point.evidence before pending)
  | release point=>
    obtain ⟨current,active,steps,evidence⟩:=point.evidence pending before
    exact .release current active steps evidence

theorem Point.residual (point : Point pid items w h v last) :
    ∃remaining,runPrefix (CreatePoints.body pid items) w h=runPrefix remaining v last := by
  cases point with
  | canonical point=>exact point.residual
  | mutation point=>exact point.residual
  | cleanup point=>exact point.residual
  | release point=>exact point.residual

noncomputable def remainder (point : Point pid items w h v last) : PrefixM Event Unit :=
  Classical.choose point.residual

theorem remainder_run (point : Point pid items w h v last) :
    runPrefix (CreatePoints.body pid items) w h=runPrefix (remainder point) v last :=
  Classical.choose_spec point.residual

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateExpanded
