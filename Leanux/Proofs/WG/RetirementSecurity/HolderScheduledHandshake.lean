import Leanux.Proofs.WG.RetirementSecurity.HolderScheduledTx
import Leanux.Proofs.WG.RetirementSecurity.HolderReceiveStep
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshakeWorkers
import Leanux.Proofs.WG.Queues.HandshakeWorker

/-! Handshake worker accounting joins the existing scheduler source history.
Both native authentication/replay branches and real peer payments retain the
separate key account, with session support derived from the owner carrier. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem handshake_step_keys : Hoare (liftWG WG.receiveStep)
    (Inv initial loans before temporary locals active h) (fun _ w=>HolderAccount temporary w.wg) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
    _ w v result run
  have support : HolderReceive.Ready temporary w.wg :=
    ⟨⟨entry.2.1,entry.2.2.1.1⟩,HandshakeEntry.of_owner entry.1.2.1 entry.1.2.2⟩
  exact ((hoare_iff_run_ambient _ _ _).mp HolderReceive.step
    w.wg w.ambient result v.wg v.ambient support native).1.1

theorem handshake_keys : Hoare
    (workerIter .receiveWorker none (liftWG WG.receiveStep) (Env.condResched .receiveWorker))
    (Inv initial loans before temporary locals active h) (fun _ w=>HolderAccount temporary w.wg) := by
  unfold workerIter
  apply hoare_bind _ _ handshake_step_keys
  intro more
  split
  · exact preserves_pure _
  · apply preserves_bind (keys_product_store (condResched_sameKernel .receiveWorker))
    intro yielded
    split <;> exact preserves_pure _

theorem handshake : PrefixPreserves (Inv initial loans before temporary locals active)
    OwnerChecks.Safe Origins.HistoryAdapters.receiveIteration := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ := HandshakeWorker.iteration_preserves initial loans before w h entry.1
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix Origins.HistoryAdapters.receiveIteration w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post
    have native := (Origins.HistoryAdapters.receiveIteration_erases w h).symm.trans run
    have keys := (hoare_iff_run _ _ _).mp handshake_keys w out.1 out.2 entry native
    have physical := (hoare_iff_run _ _ _).mp OccurrenceHandshake.iteration
      w out.1 out.2 entry.2.2.1 native
    have live := (hoare_iff_run _ _ _).mp (KeySlotLiveness.handshake_iteration (pending:=[]))
      w out.1 out.2 entry.2.2.2.2 native
    have structural := (BaseCoherence.receiveIteration_structure (BaseCoherence.view w.wg) w h rfl).choose_spec.2.2
    rw [run] at structural
    exact ⟨post,keys,physical,BaseCoherence.transport entry.2.2.2.1 structural,live⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
