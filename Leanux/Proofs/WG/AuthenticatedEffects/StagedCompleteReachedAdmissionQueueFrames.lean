import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAdmissionQueueSource

/-! The unchanged-ledger read and guard at the actual queue caller.
Native ownership and terminal completeness use the same concrete run. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation

theorem admission_queue_entry
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg)
    (read : runPrefix (Admission.actualOps.access (getPeerMixed pid)) w history = (.ok (peer,u),readHistory))
    (guarded : runPrefix (Admission.actualOps.step (branch .createDataDead peer.isDead)) u readHistory =
      (.ok (false,q),readHistory)) :
    Accounted readHistory ledger debts (⟨.unpublished,pid,items⟩ :: locals) q.wg := by
  have atRead := CreateEntry.read_peer_entry pid before.entry read
  have complete := CompleteSource.focused_complete (TxDisposition.nativeAccess (getPeerMixed pid)) w before.complete
  change Complete (runPrefix (Admission.actualOps.access (getPeerMixed pid)) w history).2 ledger at complete
  rw [read] at complete
  obtain ⟨v,actual,atGuard⟩ := CreateEntry.guard_entry .createDataDead peer.isDead atRead
  have same := actual.symm.trans guarded
  simp only [Prod.mk.injEq,Except.ok.injEq] at same
  obtain ⟨⟨_,rfl⟩,_⟩ := same
  exact ⟨atGuard,complete⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
