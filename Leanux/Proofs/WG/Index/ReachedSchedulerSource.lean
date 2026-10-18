import Leanux.Proofs.WG.Index.ReachedSchedulerAtomsSource
import Leanux.Proofs.WG.Index.EncryptCoreSource
import Leanux.Proofs.WG.Index.TxReachedSource
import Leanux.Proofs.WG.Index.PollNapiCoreSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedScheduler
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

theorem softirq_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe RxHistory.napiSoftirq := by
  apply Reached.aux_pair _ initial loans before
    (HolderAuxScheduler.softirq_preserves initial loans before)
  intro w h pre result v run
  have base := (BaseCoherence.softirq_structure (BaseCoherence.view w.wg) w h rfl).choose_spec.2.2
  simp only [run] at base
  have kept := (hoare_iff_run _ _ _).mp PollCore.softirq_ready w result v
    ⟨pre.1.2.2,pre.2.2⟩ ((RxHistory.napiSoftirq_erases w h).symm.trans run)
  exact ⟨BaseCoherence.transport pre.2.1 base,kept.2⟩

theorem encrypt_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe RxHistory.encryptIteration :=
  EncryptCore.observed initial loans before PollCore.softirq_ready

theorem decrypt_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe RxHistory.decryptIteration :=
  CryptCore.decrypt_observed PollCore.softirq_ready PollCore.irqExit_ready initial loans before

theorem ahead_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (pid : PeerId) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe (RxHistory.cryptAhead pid) := by
  rw [RxHistory.SchedulerSource.cryptAhead_factor]
  exact RxHistory.SchedulerSource.cryptAhead_preserves (fun _ _ pre=>pre.1.2.1.safe) _
    (atoms initial loans before) _ (encrypt_preserves initial loans before) pid

theorem iteration_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (activation : Activation) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe
      (RxHistory.activationIteration activation) := by
  rw [RxHistory.SchedulerSource.iteration_factor]
  exact RxHistory.SchedulerSource.iteration_preserves _ (atoms initial loans before) _ _ _ _ _
    (encrypt_preserves initial loans before) (ahead_preserves initial loans before)
    (CryptCore.tx_observed initial loans before) (decrypt_preserves initial loans before)
    (Reached.receiveIteration_preserves initial loans before) activation

theorem run_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (activation : Activation) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe
      (RxHistory.activationRun activation) := by
  rw [RxHistory.SchedulerSource.run_factor]
  exact RxHistory.SchedulerSource.run_preserves (I:=Reached.Aux initial loans before)
    (fun _ _ pre=>pre.1.2.1.safe)
    (fun _ _ _ same pre=>Reached.aux_store same pre) _ (atoms initial loans before) _
    (iteration_preserves initial loans before) activation

theorem dispatch_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (worker : Worker) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe (RxHistory.dispatch worker) := by
  rw [RxHistory.SchedulerSource.dispatch_factor]
  exact RxHistory.SchedulerSource.dispatch_preserves (I:=Reached.Aux initial loans before)
    (fun _ _ pre=>pre.1.2.1.safe)
    (fun _ _ _ same pre=>Reached.aux_store same pre) _ (atoms initial loans before) _
    (run_preserves initial loans before) worker

theorem schedule_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (stack : Option Worker) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe (RxHistory.schedule stack) := by
  rw [RxHistory.SchedulerSource.schedule_factor]
  exact RxHistory.SchedulerSource.schedule_preserves (I:=Reached.Aux initial loans before)
    (fun _ _ pre=>pre.1.2.1.safe)
    (fun _ _ _ same pre=>Reached.aux_store same pre) _ (atoms initial loans before) _ _ _
    (dispatch_preserves initial loans before) (run_preserves initial loans before)
    (softirq_preserves initial loans before) stack

theorem nested_preserves (initial : Ledger) (loans : Reservations)
    (before : List RxHistory.Event) (worker : Worker) :
    PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe
      (RxHistory.nestedResched worker) := by
  rw [RxHistory.SchedulerSource.nested_factor]
  exact RxHistory.SchedulerSource.nested_preserves (I:=Reached.Aux initial loans before)
    (fun _ _ pre=>pre.1.2.1.safe)
    (fun _ _ _ same pre=>Reached.aux_store same pre) _
    (schedule_preserves initial loans before) worker

end Leanux.Proofs.WG.Index.ReachedScheduler
