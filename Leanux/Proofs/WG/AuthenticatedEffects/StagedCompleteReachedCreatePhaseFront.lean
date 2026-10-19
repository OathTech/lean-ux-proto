import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseQueue
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePhaseAccounts

/-! Every canonical admission point derives its phase from the original
unpublished account and pending batch. The actual dead/enqueue/EPIPE branch
results select the concrete queue and publication proofs. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
open HandshakeSecurity.StagedDisposal CreatePoints
set_option maxHeartbeats 600000

theorem front_covers (steps : Staged.Obligations.Step rootLedger ledger)
    (pending : PendingBatch h ledger items)
    (before : Accounted h ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg) :
    Covers (fun h w=>Live rootLedger debts locals pid items h w.wg) (frontShape pid items) w h := by
  unfold frontShape
  apply covers_marked
  have readSafe:=atom_covers (.peer pid) trivial (.unpublished ledger steps pending before)
  apply covers_bind readSafe
  intro peer u readHistory read
  obtain ⟨atGuard,suffix,grown⟩:=access_account _ _ (getPeerMixed_erases pid) (Queued.read pid) before read
  have batch : PendingBatch readHistory ledger items := grown ▸ pending.append suffix
  have guardSafe:=atom_covers (.branch .createDataDead peer.isDead) trivial (readSafe.normal read)
  apply covers_bind guardSafe
  intro dead v guardHistory guarded
  obtain ⟨_,rfl,atQueue⟩:=guard_account .createDataDead peer.isDead atGuard guarded
  cases dead with
  | true=>exact covers_pure _ (guardSafe.normal guarded)
  | false=>
    have queued:=enqueue_covers steps batch atQueue
    apply covers_bind queued
    intro ret q last enqueued
    have pipeSafe:=atom_covers (.branch .createDataEpipe (ret == -WG.EPIPE)) trivial (queued.normal enqueued)
    apply covers_bind pipeSafe
    intro pipe r pipeHistory tested
    cases pipe with
    | false=>
      have noop : Covers (fun h w=>Live rootLedger debts locals pid items h w.wg) (Shape.pure ()) r pipeHistory :=
        covers_pure () (pipeSafe.normal tested)
      exact covers_bind noop (fun _ _ _ run=>covers_pure _ (noop.normal run))
    | true=>
      have published:=publish_covers items .dead (pipeSafe.normal tested)
      exact covers_bind published (fun _ _ _ run=>covers_pure _ (published.normal run))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePhase
