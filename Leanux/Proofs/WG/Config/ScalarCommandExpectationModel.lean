import Leanux.Proofs.WG.Config.ScalarExpectationModel
import Leanux.Proofs.WG.Config.RequestOrderModel
import Leanux.Proofs.WG.Index.ConfigurationCoreModel

/-! Projected source decision inputs and paired completed receipts. Update decisions
retain the actual full peer; births retain actual cursor/counter data. Quiet means
backward scalar retention and permits deletion or other operational work. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar.Expectation
open Leanux Leanux.WG Queues Queues.RxCredits

/-- Source decision inputs for an actual completed peer command. The update
retains the full resident peer, because endpoint equality reads cached fields. -/
def Matches (attrs : PeerAttrs) (ret : Int) (before : Campaign2.Snapshot) : Action→Prop
  | .quiet=>True
  | .update pid p input result=>
      input=attrs ∧ result=ret ∧ ∃d key,before.wg.device=some d ∧
        attrs.publicKey=some key ∧
        d.peerHashtable.find? (·.1 == key)=some (key,pid) ∧ d.peers[pid]?=some p
  | .birth pid stamp input result=>
      input=attrs ∧ result=ret ∧ stamp=before.wg.peerCounter+1 ∧
        ∃d key,before.wg.device=some d ∧ attrs.publicKey=some key ∧
          d.peerHashtable.find? (·.1 == key)=none ∧ pid=d.nextPeer

def ReceiptStep (r : RequestOrder.Receipt) (action : Action) : Prop :=
  ∃attrs,r.kind=.peer attrs ∧ Matches attrs r.result r.before action ∧
    Step action (observation r.before) (observation r.after)

inductive ReceiptSteps : List RequestOrder.Receipt→List Action→Prop
  | nil : ReceiptSteps [] []
  | cons {r action rs actions} (head : ReceiptStep r action)
      (tail : ReceiptSteps rs actions) : ReceiptSteps (r::rs) (action::actions)

def Input (cs : Ledger) (loans : Reservations) (s : Campaign2.Snapshot) : Prop :=
  Index.View.ConfigurationInput cs loans s ∧ ∃d,s.wg.device=some d

end Leanux.Proofs.WG.Config.GetterScalar.Expectation
