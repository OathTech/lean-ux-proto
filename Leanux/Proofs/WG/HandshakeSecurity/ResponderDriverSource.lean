import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverHistory
import Leanux.Proofs.WG.TransmitSecurity.DriverSource

/-! The responder projection uses the shared driver, observing only the native
session, immediate confirmation and current-key selection cuts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Packets
open TransmitSecurity

def hooks : Driver.Hooks Event where
  timerSelected := fun _ _ _ _ _ => pure 0
  selection := selection
  confirmation := confirmation
  session := session
  reserve := fun slot => liftWGPrefix (Nonce.reserveNative slot)
  allocate := fun packets => liftWGPrefix (packets.mapM newTxSkb)
  create := fun pid item => liftWGPrefix (createData pid item)
  front := fun family addr packets mtu => liftWGPrefix (txFront family addr packets mtu)
  poll := liftPrefix (liftWG TxRing.pollSource)
  encrypt := fun item => liftPrefix (RxWorkers.encryptStepTailSource item)
  transmit := fun pid => liftPrefix (liftWG (txStep pid))

def execute (trace : Runner.Trace) (placeholders : Bool) : PrefixOuter Event Lean.Json :=
  Driver.executeObserved hooks trace placeholders

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
