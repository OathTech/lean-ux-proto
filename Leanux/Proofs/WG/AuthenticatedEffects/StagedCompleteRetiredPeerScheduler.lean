import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerSchedulerAtoms
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerReceiveWorker

/-! The whole original scheduler is assembled from concrete atoms and the
remaining exact actor contracts. Every obligation names its actual observer;
TX uses its closed native exact-account proof. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Scheduler
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open Queues Queues.RxCredits Auxiliary

structure Actors (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) : Prop where
  encrypt : ExactPost initial loans before RxHistory.encryptIteration
  decrypt : ExactPost initial loans before RxHistory.decryptIteration
  softirq : ExactPost initial loans before RxHistory.napiSoftirq

theorem encrypt_preserves (actors : Actors initial loans before) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe RxHistory.encryptIteration :=
  pair _ (HolderAuxScheduler.encrypt_preserves initial loans before) actors.encrypt

theorem decrypt_preserves (actors : Actors initial loans before) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe RxHistory.decryptIteration :=
  pair _ (HolderAuxScheduler.decrypt_preserves initial loans before) actors.decrypt

theorem receive_exact : ExactPost initial loans before Origins.HistoryAdapters.receiveIteration := by
  intro w h hi x v run
  exact Handshake.iteration_owner hi.2 hi.1.2.1 hi.1.2.2 (Prod.ext run rfl)

theorem receive_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe Origins.HistoryAdapters.receiveIteration :=
  pair _ (HandshakeWorker.iteration_preserves initial loans before) receive_exact

theorem softirq_preserves (actors : Actors initial loans before) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe RxHistory.napiSoftirq :=
  pair _ (HolderAuxScheduler.softirq_preserves initial loans before) actors.softirq

theorem tx_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) (pid : PeerId) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe
      (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  pair_preserves _ (HolderAuxScheduler.tx_preserves initial loans before pid)
    (ExactAt.tx_iteration initial loans before pid)

theorem ahead_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) (actors : Actors initial loans before) (pid : PeerId) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (RxHistory.cryptAhead pid) := by
  rw [RxHistory.SchedulerSource.cryptAhead_factor]
  exact RxHistory.SchedulerSource.cryptAhead_preserves (fun _ _ hi => hi.safe) _
    (atoms initial loans before) _ (encrypt_preserves actors) pid

/-- Every dispatched actor uses the original observer. Only encryption,
decryption and NAPI retain the explicit exact-account callback obligations. -/
theorem iteration_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (actors : Actors initial loans before)
    (a : Activation) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (RxHistory.activationIteration a) := by
  rw [RxHistory.SchedulerSource.iteration_factor]
  exact RxHistory.SchedulerSource.iteration_preserves _ (atoms initial loans before) _ _ _ _ _
    (encrypt_preserves actors) (ahead_preserves initial loans before actors)
    (tx_preserves initial loans before) (decrypt_preserves actors) (receive_preserves initial loans before) a

theorem run_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (actors : Actors initial loans before)
    (a : Activation) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (RxHistory.activationRun a) := by
  rw [RxHistory.SchedulerSource.run_factor]
  exact RxHistory.SchedulerSource.run_preserves (I := Inv initial loans before) (fun _ _ hi => hi.safe)
    (fun _ _ _ same hi => store hi same) _ (atoms initial loans before) _
    (iteration_preserves initial loans before actors) a

theorem dispatch_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (actors : Actors initial loans before)
    (worker : Worker) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (RxHistory.dispatch worker) := by
  rw [RxHistory.SchedulerSource.dispatch_factor]
  exact RxHistory.SchedulerSource.dispatch_preserves (I := Inv initial loans before) (fun _ _ hi => hi.safe)
    (fun _ _ _ same hi => store hi same) _ (atoms initial loans before) _
    (run_preserves initial loans before actors) worker

theorem schedule_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (actors : Actors initial loans before)
    (stack : Option Worker) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (RxHistory.schedule stack) := by
  rw [RxHistory.SchedulerSource.schedule_factor]
  exact RxHistory.SchedulerSource.schedule_preserves (I := Inv initial loans before) (fun _ _ hi => hi.safe)
    (fun _ _ _ same hi => store hi same) _ (atoms initial loans before) _ _ _
    (dispatch_preserves initial loans before actors) (run_preserves initial loans before actors)
    (softirq_preserves actors) stack

theorem nested_preserves (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event)
    (actors : Actors initial loans before)
    (worker : Worker) :
    PrefixPreserves (Inv initial loans before) OwnerChecks.Safe (RxHistory.nestedResched worker) := by
  rw [RxHistory.SchedulerSource.nested_factor]
  exact RxHistory.SchedulerSource.nested_preserves (I := Inv initial loans before) (fun _ _ hi => hi.safe)
    (fun _ _ _ same hi => store hi same) _ (schedule_preserves initial loans before actors) worker

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Scheduler
