import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseRejected

/-! Allocation is reached from the actual selected nonce shape. Its same
ledger assignment supplies the unpublished create entry, and the concrete
CreatePhase certificate supplies each returned create cut. Native allocator
aliases and the expanded create children retain their separate fixed-point
certificates; no idle account is asserted inside the allocator. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier AllocatedObligation Staging.Points
set_option maxHeartbeats 600000

theorem create_child_covers (steps : Staged.Obligations.Step root assigned)
    (pending : CreateDisposal.PendingBatch h assigned items)
    (before : Accounted h assigned debts (⟨.unpublished,pid,items⟩::locals) w) (a : Ambient) :
    Covers (Evidence root debts locals) (.child (.create pid items)) w a h := by
  refine ⟨.created assigned steps (.unpublished assigned (.refl _) pending before),?_⟩
  intro value v b last run
  change ((runPrefix (CreatePoints.body pid items) (NativeAdapter.world w a) h).1.map
    (fun (x,q)=>((x,q.wg),q.ambient)),(runPrefix (CreatePoints.body pid items) (NativeAdapter.world w a) h).2)=_ at run
  cases actual : runPrefix (CreatePoints.body pid items) (NativeAdapter.world w a) h with
  | mk out history=>
    rw [actual] at run
    cases out with
    | error stop=>cases run
    | ok pair=>
      obtain ⟨returned,q⟩:=pair
      cases run
      exact .created assigned steps ((CreatePhase.create_covers pending before).normal actual)

theorem submitted_covers
    (before : CompleteSelected.Ready ledger debts locals generation pid peer position h w a)
    (steps : Staged.Obligations.Step root ledger)
    (shape : BatchPayload.Shape pid kid peer.staged packets) :
    Covers (Evidence root debts locals) (tailShape pid peer (.submit kid packets)) w a h := by
  obtain ⟨items,q,performed,_,assignedStep,accounted,pending,_⟩:=Allocation.allocate_intervals before shape
  change Covers _ (.bind (.child (.allocate packets)) (fun ids=>.child (.create pid ids))) w a h
  have first : Covers (Evidence root debts locals) (.child (.allocate packets)) w a h := by
    refine ⟨.selected ledger steps before,?_⟩
    intro ids u b middle run
    rw [performed] at run
    cases run
    exact .created _ (steps.trans assignedStep) (.unpublished _ (.refl _) pending accounted)
  apply covers_bind first
  intro ids u b middle run
  rw [performed] at run
  cases run
  exact create_child_covers (steps.trans assignedStep) pending accounted a

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
