import Leanux.Proofs.WG.Index.ConfigurationIndexModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux
open Queues.RxCredits
open Queues.RxCredits.DurableHolders

/-- The exact projection realizes the current account, configuration, base,
slot and index assumptions. Reachability from initialization is separate. -/
def View.ConfigurationInput (cs : Ledger) (loans : Reservations) (s : Campaign2.Snapshot) : Prop :=
  ∃ w a, Campaign2.snapshot w a=s ∧ ConfigurationIndex.Entry cs loans w

end Leanux.Proofs.WG.Index
