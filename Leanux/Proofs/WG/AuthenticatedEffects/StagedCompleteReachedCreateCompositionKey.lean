import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreateCompositionCalls
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedKeyAccessAdapter

/-! Creation's source family includes its concrete key-repayment interiors.
The same original unpublished entry supplies each child phase. Peer-release
and packet-free interiors remain separate obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateComposition
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open AllocatedObligation CompleteCarrier

inductive Point (pid : PeerId) (items : List SkbId) (w : World) (h : List Event) :
    World → List Event → Prop where
  | base (point : CreatePoints.Point (CreatePoints.createShape pid items) w h leaf v middle rest) :
      Point pid items w h v middle
  | repay (call : Call (CreatePoints.createShape pid items) w h (.repay kid) u prior context)
      (point : KeyAccess.RootPoint kid false u prior v middle) : Point pid items w h v middle

/-- The actual creation entry derives every declared phase, including the
native key repayment before access receipts, on the original ticket lineage. -/
theorem Point.live (pending : CreateDisposal.PendingBatch h ledger items)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (point : Point pid items w h v middle) : CreatePhase.Live ledger debts locals pid items middle v.wg := by
  cases point with
  | base point=>exact (CreatePhase.create_covers pending before).point point
  | repay call point=>exact point.live (call.entry (CreatePhase.create_covers pending before))

theorem Point.residual (point : Point pid items w h v middle) :
    ∃rest,runPrefix (CreatePoints.body pid items) w h=runPrefix rest v middle := by
  cases point with
  | base point=>exact ⟨_,point.residual⟩
  | repay call point=>
    obtain ⟨rest,source⟩:=point.residual
    exact ⟨_,call.resume source⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateComposition
