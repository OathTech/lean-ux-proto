import Leanux.Proofs.WG.RetirementSecurity.HolderScheduledRx
import Leanux.Proofs.WG.Queues.HolderEncryptHistory

/-! Encryption transports key credit across its actual ring dequeue and
intervening NAPI callback. The consumed batch is retained as an explicit
active alias until the native encryption/publication continuation completes. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderEncryptKeys
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits
open CurrentLifecycle CurrentTraffic

theorem poll_current : Preserves (CurrentLifecycle.Inv sessions) TxRing.pollSource := by
  unfold TxRing.pollSource
  repeat' current_lifecycle_step sessions

theorem poll_support (before : HolderPoll.Support sessions locals active w) (a b : Ambient)
    (run : (TxRing.pollSource.run w).run a=.ok ((item,v),b)) :
    HolderPoll.Support sessions locals (item.toList++active) v :=
  ⟨OccurrenceEncrypt.poll before.1 a b run,
    (hoare_iff_run_ambient _ _ _).mp poll_current w a item v b before.2.1 run,
    BaseCoherence.transport before.2.2.1
      ((ProjectedAction.iff_run_ambient _ _ _).mp BaseCoherence.encryptPoll_view w a item v b run),
    (hoare_iff_run_ambient _ _ _).mp (KeySlotLiveness.encrypt_poll (pending:=[])) w a item v b before.2.2.2 run⟩

theorem tail_store {action : Leanux.M α} (same : SameProductStore action) :
    Preserves (fun w:World=>HolderAccount temporary w.wg ∧ TxInventory locals w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  have device := congrArg (fun s:ProductStore43=>s.2.2.2.dev)
    ((ProjectedAction.iff_run _ _ _).mp same w result v run)
  change v.wg.dev=w.wg.dev at device
  have points : ownershipPointView v.wg=ownershipPointView w.wg := by
    unfold ownershipPointView ownershipAt peerAt keyReferenceView keyAt packetKeyWords
    rw [device]
  exact ⟨before.1.points points,before.2.points points⟩

theorem tail_keys (item : Option (List SkbId)) :
    Preserves (fun w:World=>HolderAccount temporary w.wg ∧ TxInventory locals w.wg)
      (RxWorkers.encryptTailSource item) := by
  let P := fun w:World=>HolderAccount temporary w.wg ∧ TxInventory locals w.wg
  have step : Preserves P (RxWorkers.encryptStepTailSource item) := encrypt_tail_accounts item
  have need : Preserves P (Env.condResched .encryptWorker) := tail_store (condResched_sameKernel _)
  have ambient {α:Type} (a:AmbientM α) : Preserves P (monadLift a:Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ before=>before)
  change Preserves P _
  routing_tx_source [RxWorkers.encryptTailSource,workerIter] using [step,need,ambient]

theorem iteration_keys
    (entry : HolderNapiKeys.Inv sessions locals active temporary initial loans before h w)
    (run : runPrefix RxHistory.encryptIteration w h=(.ok (result,v),k)) : HolderAccount temporary v.wg := by
  unfold RxHistory.encryptIteration at run
  obtain ⟨item,polled,polledHistory,pollRun,rest⟩ := DecryptIteration.bind_normal run
  have nativePoll := HolderPoll.native_receipt
    ((RxHistory.mixed_erases (liftWGObserver_erases (erasesStatePrefix_lift TxRing.pollSource)) w h).symm.trans
      (congrArg Prod.fst pollRun))
  have first := HolderEncrypt.mixed_at _ _ (liftWGObserver_erases (erasesStatePrefix_lift TxRing.pollSource))
    (fun _=>HolderEncrypt.lift_boundary (HolderEncrypt.native_boundary HolderEncrypt.poll_fields)) entry.1 pollRun
  have keyPoll := entry.2.1.points ((ProjectedAction.iff_run_ambient _ _ _).mp OccurrenceEncrypt.poll_points
    w.wg w.ambient item polled.wg polled.ambient nativePoll)
  have supportPoll := poll_support entry.2.2 w.ambient polled.ambient nativePoll
  obtain ⟨u,received,receivedHistory,napiRun,tailRun⟩ := DecryptIteration.bind_normal rest
  cases u
  have middle := HolderDecryptKeys.softirq_at
    (show HolderNapiKeys.Inv sessions locals (item.toList++active) temporary initial loans before polledHistory polled from
      ⟨first,keyPoll,supportPoll⟩) napiRun
  have tailNative := (RxHistory.mixed_erases (RxWorkers.encryptTail_erases item) received receivedHistory).symm.trans
    (congrArg Prod.fst tailRun)
  exact ((hoare_iff_run _ _ _).mp (tail_keys item) received result v
    ⟨middle.2.1,middle.2.2.1.2.1⟩ tailNative).1

end Leanux.Proofs.WG.RetirementSecurity.HolderEncryptKeys

namespace Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem encrypt : PrefixPreserves (Inv initial loans before temporary locals active)
    OwnerChecks.Safe RxHistory.encryptIteration := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ := HolderAuxScheduler.encrypt_preserves initial loans before w h entry.1
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix RxHistory.encryptIteration w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post
    have keys := HolderEncryptKeys.iteration_keys (napi_entry entry) (Prod.ext run rfl)
    have native := (RxHistory.encryptIteration_erases w h).symm.trans run
    have physical := (hoare_iff_run _ _ _).mp OccurrenceEncrypt.iteration w out.1 out.2 entry.2.2.1 native
    have live := (hoare_iff_run _ _ _).mp (KeySlotLiveness.encrypt_iteration (pending:=[]))
      w out.1 out.2 entry.2.2.2.2 native
    have structural := (BaseCoherence.encryptIteration_structure (BaseCoherence.view w.wg) w h rfl).choose_spec.2.2
    rw [run] at structural
    exact ⟨post,keys,physical,BaseCoherence.transport entry.2.2.2.1 structural,live⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
