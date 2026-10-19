import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreateCompositionKey
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNestedPeerPoints

/-! Creation's nested peer-release entries come from the fixed canonical
call path. That same invocation supplies the account; no peer-release
callback contract or newly chosen ledger is an incoming premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateComposition
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open AllocatedObligation CompleteCarrier

inductive ReleasePoint (pid : PeerId) (items : List SkbId) (w : World) (h : List Event) :
    World → List Event → Prop where
  | source (call : Call (CreatePoints.createShape pid items) w h (.release peer) u prior context)
      (point : NestedPeer.Point peer u prior v middle) : ReleasePoint pid items w h v middle

/-- Every fixed nested release point has ownership or its actual pending
disposal receipt on the original creation ledger's successor lineage. -/
theorem ReleasePoint.evidence (pending : CreateDisposal.PendingBatch h ledger items)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (point : ReleasePoint pid items w h v middle) :
    ∃current active,Staged.Obligations.Step ledger current ∧
      NestedPeer.Evidence current debts active middle v := by
  cases point with
  | source call point=>
    obtain ⟨current,active,step,account⟩:=(call.entry (CreatePhase.create_covers pending before)).accounted
    exact ⟨current,active,step,point.evidence account⟩

theorem ReleasePoint.residual (point : ReleasePoint pid items w h v middle) :
    ∃remaining,runPrefix (CreatePoints.body pid items) w h=runPrefix remaining v middle := by
  cases point with
  | source call point=>
    obtain ⟨remaining,residual⟩:=point.residual
    exact ⟨_,call.resume residual⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreateComposition
