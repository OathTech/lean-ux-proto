import Leanux.Proofs.WG.Index.ConfigurationCoreModel
import Leanux.Proofs.WG.Index.ReceiverCoreBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux
open Queues.RxCredits
open Queues.RxCredits.DurableHolders

theorem configurationInput_snapshot (cs : Ledger) (loans : Reservations) (w : WGWorld) (a : Ambient) :
    View.ConfigurationInput cs loans (Campaign2.snapshot w a) ↔ ConfigurationIndex.Entry cs loans w := by
  constructor
  · rintro ⟨v,b,same,entry⟩
    exact receiveInput_world (congrArg Campaign2.Snapshot.wg same) ▸ entry
  · intro entry
    exact ⟨w,a,rfl,entry⟩

end Leanux.Proofs.WG.Index
