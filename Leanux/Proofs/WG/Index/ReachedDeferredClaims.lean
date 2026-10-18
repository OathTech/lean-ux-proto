import Leanux.Proofs.WG.Index.ReachedDeferredEntrySource
import Leanux.Proofs.WG.Index.ReachedSchedulerClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem deferred_index (initial : Ledger) (loans : Reservations)
    (before history : List RxHistory.Event) (call : EnvDeferredCall) :
    Campaign2.Product.Ensures call.original
      (fun s=>View.SchedulerInput initial loans before history s.toSnapshot)
      (fun _ s=>View.IndexCore s.toSnapshot) :=
  observed_index_core initial loans before history _ _ (RxHistory.deferred_erases call)
    (ReachedDeferred.deferred initial loans before call)

end Leanux.Proofs.WG.Index
