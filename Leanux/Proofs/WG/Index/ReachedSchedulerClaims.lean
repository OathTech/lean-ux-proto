import Leanux.Proofs.WG.Index.ReachedSchedulerSource
import Leanux.Proofs.WG.Index.ReachedSchedulerBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem observed_index_core {α : Type} (initial : Ledger) (loans : Reservations)
    (before history : List RxHistory.Event) (observed : RxHistory.Obs α) (action : Leanux.M α)
    (erase : ErasesPrefix observed action)
    (keep : PrefixPreserves (Reached.Aux initial loans before) OwnerChecks.Safe observed) :
    Campaign2.Product.Ensures action
      (fun s=>View.SchedulerInput initial loans before history s.toSnapshot)
      (fun _ s=>View.IndexCore s.toSnapshot) := by
  intro w result v pre run
  have post := (keep w history ((schedulerInput_snapshot initial loans before history w).mp pre)).choose_spec.2.2
  have actual := (erase w history).trans run
  rw [actual] at post
  exact post.2.2

theorem scheduler_index (initial : Ledger) (loans : Reservations)
    (before history : List RxHistory.Event) (stack : Option Worker) :
    Campaign2.Product.Ensures (Env.schedule stack)
      (fun s=>View.SchedulerInput initial loans before history s.toSnapshot)
      (fun _ s=>View.IndexCore s.toSnapshot) :=
  observed_index_core initial loans before history _ _ (RxHistory.schedule_erases stack)
    (ReachedScheduler.schedule_preserves initial loans before stack)

theorem nested_scheduler_index (initial : Ledger) (loans : Reservations)
    (before history : List RxHistory.Event) (worker : Worker) :
    Campaign2.Product.Ensures (Env.nestedResched worker)
      (fun s=>View.SchedulerInput initial loans before history s.toSnapshot)
      (fun _ s=>View.IndexCore s.toSnapshot) :=
  observed_index_core initial loans before history _ _ (RxHistory.nestedResched_erases worker)
    (ReachedScheduler.nested_preserves initial loans before worker)

theorem tx_iteration_index (initial : Ledger) (loans : Reservations)
    (before history : List RxHistory.Event) (pid : PeerId) :
    Campaign2.Product.Ensures (txIter pid (Env.condResched .txWorker))
      (fun s=>View.SchedulerInput initial loans before history s.toSnapshot)
      (fun _ s=>View.IndexCore s.toSnapshot) :=
  observed_index_core initial loans before history _ _
    (RxHistory.mixed_erases (txIterPrefix_erases pid (erasesPrefix_lift (Env.condResched .txWorker))))
    (CryptCore.tx_observed initial loans before pid)

end Leanux.Proofs.WG.Index
