import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerSafety
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryBase
import Leanux.Proofs.WG.TransmitSecurity.DriverNeutralCalls

/-! Authentication-root specialization of the one shared driver. Native hooks
are quiet in this projection; handshake callbacks retain their own admissions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeDriver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Packets
open TransmitSecurity

def hooks : Driver.Hooks HandshakeCausal.Event where
  handshake := HandshakeWorker.observed id some
  timerSelected := fun _ _ _ _ _ => pure 0
  selection := fun pid => liftWGPrefix (HandshakeSecurity.Responder.selectionPrefix pid)
  confirmation := fun pid kid => liftWGPrefix (receivedWithKeypair pid kid)
  session := fun pid => liftWGPrefix (beginSession pid)
  reserve := fun slot => liftWGPrefix (Nonce.reserveNative slot)
  allocate := fun packets => liftWGPrefix (packets.mapM newTxSkb)
  create := fun pid item => liftWGPrefix (createData pid item)
  front := fun family addr packets mtu => liftWGPrefix (txFront family addr packets mtu)
  poll := liftPrefix (liftWG TxRing.pollSource)
  encrypt := fun item => liftPrefix (RxWorkers.encryptStepTailSource item)
  transmit := fun pid => liftPrefix (liftWG (txStep pid))

/-- Security: every hook in the authentication-root specialization preserves
valid earlier causes; the handshake hook proves its callbacks from the actual
consumer admission, and all other hooks leave this projected history unchanged. -/
theorem hooks_safe : Driver.HooksHistorySafe HandshakeCausal.Safe hooks := by
  constructor
  · intro trigger; exact Driver.History.state_pure _
  · intro token; exact Driver.History.state_pure _
  · exact HandshakeWorker.HistorySafety.observed_preserves
  all_goals intros
  all_goals first
    | assumption
    | (rw [Driver.sendWorker_lift hooks rfl]; exact Driver.History.product_lift _)
    | exact Driver.History.state_lift _
    | exact Driver.History.product_lift _
    | exact Driver.History.product_state (Driver.History.state_lift _)
    | exact Driver.History.product_pure _

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeDriver
