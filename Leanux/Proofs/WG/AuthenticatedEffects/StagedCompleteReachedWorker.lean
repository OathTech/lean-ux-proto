import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedBatch
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedContracts
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSnapshotFrames

/-! The crypted-worker conversion retains a constructor-matched completion
cut. `WorkerProjection` does not assert the stronger operational `At` relation:
that evidence must be threaded through the checked leaf and loop contracts.
In particular, the old history-only Stop predicate cannot recover it. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation AllocatedObligation.CompletionBatch
open AllocatedObligation.CompletionBatch.Converse

structure WorkerProjection (ledger : Ledger) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (head : DataPacket) (w : World)
    (history : List CausalJournal.Event) (reason : Stop) (last : List CausalJournal.Event)
    (context : Context) (saved : Cut context) : Prop where
  peer : context.pid = pid
  localEq : context.locals = locals
  itemsEq : context.items = items
  initial : context.initialLedger = ledger
  domain : context.births = births history
  owned : Owned context (.sending context.items) history ledger [] w
  complete : Complete history ledger
  branch : BatchProjection context ledger head.keypair w history reason last saved

theorem worker_project
    (failure : Converse.WorkerFailure ledger locals pid items head w history reason last) :
    ∃ context saved, WorkerProjection ledger locals pid items head w history reason last context saved := by
  obtain ⟨context,peer,localEq,itemsEq,initial,domain,owned,complete,stopped⟩ := failure
  obtain ⟨saved,branch⟩ := batch_project stopped
  exact ⟨context,saved,peer,localEq,itemsEq,initial,domain,owned,complete,branch⟩

theorem WorkerProjection.original
    (projection : WorkerProjection ledger locals pid items head w history reason last context saved) :
    Converse.WorkerFailure ledger locals pid items head w history reason last :=
  ⟨context,projection.peer,projection.localEq,projection.itemsEq,projection.initial,
    projection.domain,projection.owned,projection.complete,projection.branch.original⟩

theorem WorkerProjection.valid
    (projection : WorkerProjection ledger locals pid items head w history reason last context saved) :
    saved.Valid reason last := projection.branch.valid

theorem WorkerProjection.step
    (projection : WorkerProjection ledger locals pid items head w history reason last context saved) :
    Staged.Obligations.Step ledger saved.ledger := projection.branch.step

/-- The account uses this branch's native saved world, ledger and phase.
Its active caller local is the exact phase projection of this selected batch. -/
theorem WorkerProjection.accounted
    (projection : WorkerProjection ledger locals pid items head w history reason last context saved) :
    Accounted last saved.ledger saved.debts
      (⟨.selected,pid,saved.phase.active context⟩ :: locals) saved.world.wg := by
  simpa only [Cut.locals,projection.peer,projection.localEq] using projection.valid.accounted

/-- The upgraded local failure predicate preserves the matched cut rather
than immediately replacing it by an independent existential accounted world. -/
def WorkerStopped : TxWorker.CryptFailure := fun ledger locals pid items head w history reason last =>
  ∃ context saved, WorkerProjection ledger locals pid items head w history reason last context saved

theorem crypted_projected : CryptContract WorkerStopped := by
  intro ledger locals pid items head w history entry complete pending ready
  have checked := crypted_contract ledger locals pid items head w history entry complete pending ready
  cases performed : runPrefix (TxWorker.crypted pid items head) w history with
  | mk result last =>
    rw [performed] at checked
    cases result with
    | error reason => exact worker_project checked
    | ok out => exact checked

/-- Preserve the bind-decomposition path to this very saved cut. Native
source provenance still needs a concrete interval or receipt anchor; neither
that provenance nor this path is inferred from history-prefix inclusion. -/
theorem WorkerProjection.reached
    (projection : WorkerProjection ledger locals pid items head w history reason last context saved)
    (entry : At saved.action.source saved.world saved.before
      (TxWorker.crypted pid items head) w history) :
    Nonempty (Failure context (TxWorker.crypted pid items head) w history reason last) :=
  ⟨⟨saved,projection.valid,entry⟩⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
