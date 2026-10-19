import Leanux.Proofs.WG.Config.PeerScalarRetentionModel
import Leanux.Proofs.WG.Index.ConfigurationCoreModel

/-! Scalar semantics at the actual acquired finish cut. Selected is a backward surviving-cell predicate; FinishInput supplies the initial account and base-list occurrence, not final survival. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarFinish
open Leanux Leanux.WG Noise Std.Do
open Queues Queues.RxCredits Leanux.Proofs.Framing Lifetimes
open PeerScalarRetention

def Selected (pid : PeerId) (expected : Cell) (values : Map) : Prop :=
  ∀ c, values pid=some c → c=expected

def intervalCell (expected : Cell) (interval : Nat) : Cell :=
  (expected.1,expected.2.1,interval,expected.2.2.2)

def finishCell (attrs : PeerAttrs) (expected : Cell) : Cell :=
  intervalCell expected (attrs.keepalive.getD expected.2.2.1)

def FinishInput (cs : Ledger) (loans : Reservations) (paid : Owner)
    (expected : Cell) (s : Campaign2.Snapshot) : Prop :=
  Index.View.ConfigurationInput cs (paid::loans) s ∧
  paid.slot∈(s.wg.device.map Device.peerList).getD [] ∧
  observation s paid.slot=some expected

end Leanux.Proofs.WG.Config.ScalarFinish
