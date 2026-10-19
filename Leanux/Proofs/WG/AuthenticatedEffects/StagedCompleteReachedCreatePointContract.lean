import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointResidual
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointMark
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointPublication
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointRefusal

/-! Canonical create coverage and its concrete named boundary accounts.
The execution tree covers normal and stopped source branches unconditionally.
Uncrypted marking, pre-receipt peer-queue installation, EPIPE publication and
ordered refused frees have same-ledger source joins. This does not assert an
idle account at every Point: key repayment, peer release and the interiors
of native atoms remain explicit children, except for the mutation cuts proved
here. Initialized caller coverage and a universal phase carrier are separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations CausalJournal
set_option maxHeartbeats 600000

/-- A source point has an actual saved native world and original continuation.
The attached account is specifically the invocation's unpublished entry;
post-erase worlds instead use FreeCut.pending_receipt. -/
structure CreatePoint (history : History) (ledger : Ledger) (debts : List CleanupDebt)
    (locals : List TxLocalBatch) (pid : PeerId) (items : List SkbId) (w : World) : Type 1 where
  entry : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg
  pending : PendingBatch history ledger items
  valueType : Type
  leaf : PrefixM Event valueType
  world : World
  journal : History
  remaining : PrefixM Event Unit
  source : Point (createShape pid items) w history leaf world journal remaining

theorem CreatePoint.original
    (point : CreatePoint history ledger debts locals pid items w) :
    runPrefix (body pid items) w history=runPrefix point.remaining point.world point.journal := point.source.residual

theorem CreatePoint.lowered
    (point : CreatePoint history ledger debts locals pid items (NativeAdapter.world w a)) :
    runWGPrefix (CausalJournal.create pid items) w a history=
      ((runPrefix point.remaining point.world point.journal).1.map (fun (value,v)=>((value,v.wg),v.ambient)),
        (runPrefix point.remaining point.world point.journal).2) := point.source.lowered

/-- Exact result-aware canonical coverage from the concrete pending batch.
A stopped execution retains the real empty/admission/repayment frontier; a
normal one retains the same successor ledger and actual named dispositions. -/
theorem create_checked
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (pending : PendingBatch history ledger items) :
    let actual:=runPrefix (body pid items) w history
    Execution (createShape pid items) w history actual.1 actual.2 ∧
      match actual.1 with
      | .error reason=>CompleteCreate.CreatedStop ledger debts locals pid items w history reason actual.2
      | .ok ((),v)=>CompleteCreate.CreatedReturned ledger debts locals pid items w history actual.2 v :=
  ⟨create_cases pid items w history,CompleteCreate.create_cases pid items before pending⟩

/-- Type-valued fixed source execution witness. Its result and final journal
are definitionally those of the original callback; it cannot select another
history/world by an extensional factorization. The semantic frontier remains
result-aware and does not supply a post-error World. -/
structure SourceExecution (history : History) (ledger : Ledger) (debts : List CleanupDebt)
    (locals : List TxLocalBatch) (pid : PeerId) (items : List SkbId) (w : World) : Type 1 where
  entry : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg
  pending : PendingBatch history ledger items
  trace : let actual:=runPrefix (body pid items) w history
    Execution (createShape pid items) w history actual.1 actual.2
  frontier : let actual:=runPrefix (body pid items) w history
    match actual.1 with
    | .error reason=>CompleteCreate.CreatedStop ledger debts locals pid items w history reason actual.2
    | .ok ((),v)=>CompleteCreate.CreatedReturned ledger debts locals pid items w history actual.2 v

noncomputable def source_execution
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (pending : PendingBatch history ledger items) : SourceExecution history ledger debts locals pid items w :=
  ⟨before,pending,(create_checked before pending).1,(create_checked before pending).2⟩

/-- No normal completion of creation is assumed when decomposing a Stop.
The last journal belongs to the actual failed source branch. -/
theorem stopped_checked
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (pending : PendingBatch history ledger items)
    (failed : runPrefix (body pid items) w history=(.error reason,last)) :
    Execution (createShape pid items) w history (.error reason) last ∧
      CompleteCreate.CreatedStop ledger debts locals pid items w history reason last := by
  have result:=create_checked before pending
  dsimp only at result
  rw [failed] at result
  exact result

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
