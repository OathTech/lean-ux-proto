import Leanux.Proofs.WG.Queues.HandshakeReception
import Leanux.Proofs.WG.Queues.HandshakeSlotHistory
import Leanux.Proofs.WG.Queues.HolderAuxScheduler

/-! The actual handshake ring step keeps its dequeue before receive and its
queue-length decrement afterwards. Its funding uses the actual input Entry;
its original observer retains the fixed removal cut and physical RX ring. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HandshakeWorker
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders HandshakeResponse

private theorem install (ring : PtrRing (List UInt8 × SkbSource)) :
    Preserves (Input cs loans) (modifyDev fun d => {d with handshakeQueue:=ring}) := by
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeSendResponse.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeSendResponse.join)
  · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceive.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceive.modifyDevice)
    intro w
    unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
    unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
    cases hd : w.dev <;> simp [hd,rxView]
  · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine)
    · apply (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.modifyDevice)
      all_goals intro d; rfl
    · apply CurrentSlots.fields_preserves (project := id)
      intro initial
      change Preserves (fun w => CurrentSlots.fields w = initial) _
      slot_fields_step initial

private theorem decrement : Preserves (Boundary cs loans)
    (modifyDev fun d => {d with handshakeQueueLen:=d.handshakeQueueLen-1}) := by
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceive.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceive.modifyDevice)
  intro w
  unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  cases hd : w.dev <;> simp [hd,rxView]

/-- Empty polls return normally without acquiring a peer. A consumed packet
runs the unchanged receiver with the account and auxiliary input intact. -/
theorem native_step : Hoare WG.receiveStep (Input cs loans) (fun _ => Boundary cs loans) := by
  unfold WG.receiveStep
  apply hoare_bind _ _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReception.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReception.store) getDev_sameWGStore)
  intro d
  cases outcome : d.handshakeQueue.consume with
  | mk item ring =>
    cases item with
    | none =>
      apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .workerConsumed false) (Input cs loans))
      intro _
      apply hoare_consequence (hoare_pure false (Input cs loans))
      · exact fun _ hi => hi
      · exact fun _ _ hi => hi.2.1
    | some item =>
      obtain ⟨msg,src⟩ := item
      apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .workerConsumed true) (Input cs loans))
      intro _
      apply hoare_bind _ _ (install ring)
      intro _
      apply hoare_bind _ _ (HandshakeReception.receive msg src)
      intro _
      exact preserves_bind decrement (fun _ => preserves_pure true)

/-- The original handshake observer emits lifetime/session records, never an
RX consume/drop removal. The existing incoming journal is retained exactly. -/
theorem step_quiet : HistoryFrame NapiCarrier.removed Origins.HistoryAdapters.receiveStep := by
  intro w h
  unfold Origins.HistoryAdapters.receiveStep Origins.HistoryAdapters.focus
  exact focusPrefix_other Origins.HistoryAdapters.encode Origins.HistoryAdapters.decode
    NapiCarrier.removed (fun e => by cases e <;> rfl) _ w h

/-- Funding and the physical witness use the same actual run as the original
owner journal. This endpoint contract does not claim slot transport. -/
theorem step_normal (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : runPrefix Origins.HistoryAdapters.receiveStep w h = (.ok (result,v),k)) :
    HolderScheduler.Inv initial loans before k v := by
  have native := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
    WG.receiveStep w v result
    ((Origins.HistoryAdapters.receiveStep_erases w h).symm.trans (congrArg Prod.fst run))
  obtain ⟨old,history,boundary⟩ := hi.1.1
  have post := (hoare_iff_run_ambient _ _ _).mp native_step
    w.wg w.ambient result v.wg v.ambient
    ⟨boundary,HandshakeEntry.of_owner hi.2.1 hi.2.2⟩ native
  have account := HolderDecryptHistory.quiet_cut (Appends.focus _ _ _) step_quiet history run post
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp RxRing.receiveStep_cell
    w.wg w.ambient result v.wg v.ambient native
  obtain ⟨epoch,n,events,ring,refines,cell⟩ := hi.1.2
  exact ⟨account,epoch,n,events,ring,refines,same.trans cell⟩

/-- All three normal iteration outcomes retain the same committed ledger cut.
The source reschedule call changes neither the receive journal nor WG store. -/
theorem iteration_normal (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : runPrefix Origins.HistoryAdapters.receiveIteration w h = (.ok (result,v),k)) :
    HolderScheduler.Inv initial loans before k v := by
  unfold Origins.HistoryAdapters.receiveIteration workerIterPrefix at run
  obtain ⟨more,u,j,step,tail⟩ := DecryptIteration.bind_normal run
  have post := step_normal hi step
  cases more with
  | false =>
    simp only [Bool.not_false,ite_true] at tail
    cases tail
    exact post
  | true =>
    simp only [Bool.not_true,Bool.false_eq_true,ite_false] at tail
    obtain ⟨yielded,z,l,reschedule,done⟩ := DecryptIteration.bind_normal tail
    cases done
    simp only [runPrefix_lift,Prod.mk.injEq] at reschedule
    obtain ⟨actual,rfl⟩ := reschedule
    exact HolderScheduler.store post
      ((ProjectedAction.iff_run _ _ _).mp (condResched_sameKernel .receiveWorker) u yielded _ actual)

/-- The original journal retains its existing owner checks even on a Stop.
Normal endpoints additionally retain the complete holder account and ring;
slot preservation is intentionally left to its independent source proof. -/
theorem iteration_ensures (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) :
    PrefixEnsures (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      Origins.HistoryAdapters.receiveIteration
      (fun _ h w => HolderScheduler.Inv initial loans before h w ∧ OwnerChecks.Inv h w) := by
  intro w h hi
  obtain ⟨suffix,history,safe,owner⟩ := OwnerHandshake.receiveIteration w h hi.2.1
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix Origins.HistoryAdapters.receiveIteration w h).1 with
  | error e => trivial
  | ok out =>
    rw [run] at owner
    exact ⟨iteration_normal hi (Prod.ext run rfl),owner⟩

/-- The funded endpoint and slot endpoint come from this identical original
receive iteration. This discharges the stronger scheduler's receive premise. -/
theorem iteration_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      Origins.HistoryAdapters.receiveIteration := by
  intro w h hi
  obtain ⟨suffix,history,safe,account⟩ := iteration_ensures initial loans before w h hi
  refine ⟨suffix,history,safe,?_⟩
  cases run : (runPrefix Origins.HistoryAdapters.receiveIteration w h).1 with
  | error e => trivial
  | ok out =>
    rw [run] at account
    have slots := HandshakeSlotHistory.receiveIteration_normal hi.2.1 hi.2.2 (Prod.ext run rfl)
    exact ⟨account.1,account.2,slots.2⟩

/-- The unchanged scheduler source now has its actual receive callback closed.
All incoming committed histories and the fixed accounting cut remain explicit. -/
theorem activationIteration (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (activation : Activation) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (RxHistory.activationIteration activation) :=
  HolderAuxScheduler.iteration_preserves initial loans before
    (iteration_preserves initial loans before) activation

theorem activationRun (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (activation : Activation) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (RxHistory.activationRun activation) :=
  HolderAuxScheduler.run_preserves initial loans before
    (iteration_preserves initial loans before) activation

theorem dispatch (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (worker : Worker) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (RxHistory.dispatch worker) :=
  HolderAuxScheduler.dispatch_preserves initial loans before
    (iteration_preserves initial loans before) worker

theorem schedule (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (stack : Option Worker) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (RxHistory.schedule stack) :=
  HolderAuxScheduler.schedule_preserves initial loans before
    (iteration_preserves initial loans before) stack

theorem nestedResched (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (worker : Worker) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (RxHistory.nestedResched worker) :=
  HolderAuxScheduler.nested_preserves initial loans before
    (iteration_preserves initial loans before) worker

end Leanux.Proofs.WG.Queues.RxCredits.HandshakeWorker
