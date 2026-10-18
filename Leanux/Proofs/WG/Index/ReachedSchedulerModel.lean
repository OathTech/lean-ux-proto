import Leanux.Proofs.WG.Index.ReachedIndexBridge
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.View
open Leanux Queues Queues.RxCredits

/-- The supplied scheduler cut, represented by the campaign snapshot.
The existential witness is only a proof index: the bridge proves equivalence
for every realization of the same WG projection, independent of other subsystems. -/
def SchedulerInput (initial : Ledger) (loans : Reservations)
    (before history : List RxHistory.Event) (s : Campaign2.Snapshot) : Prop :=
  ∃ w : World, Campaign2.snapshot w.wg w.ambient=s ∧ Reached.Aux initial loans before history w

end Leanux.Proofs.WG.Index.View
