import Leanux.Proofs.WG.Index.CreatorCompatibleModel
import Leanux.Proofs.WG.Index.RetirementPaymentSource
import Leanux.Proofs.WG.Index.SelectedDrainFrames
import Leanux.Proofs.WG.Queues.HolderSendDispatch
import Leanux.Proofs.WG.Origins.ConfiguredRemoval

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Leanux.Proofs.Framing Leanux.Proofs.Logged
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

/-- The three local index obligations retained across an outgoing send. -/
def SendIndexSafe (retired : Reservations) (w : WGWorld) : Prop :=
  (∀ d, w.dev = some d → HashSlotCoverage d) ∧
  (∀ d, w.dev = some d → HashedOwnersCoherent d) ∧
  (∀ d, w.dev = some d → DeadHashedReserved retired d)

/-- Explicit remaining outgoing-call obligation. It concerns the original
initiation, with its actual selected loan, rather than a replacement callback. -/
def InitiationIndexContract (holders : DurableHolders) (cs : Ledger) (paid : Owner)
    (retired loans : Reservations) : Prop :=
  Ensures (sendHandshakeInitiation paid.slot)
    (fun w => ConfiguredIdentity.Inv w ∧ BaseCoherence.Inv w ∧
      holders.Funded cs (paid :: (retired ++ loans)) w ∧ StableRx cs w ∧
      SendIndexSafe retired w)
    (fun _ w => SendIndexSafe retired w)

/-- Exact native dequeue and paired pending-flag update. -/
def sendPreparedDevice (d : Device) (pid : PeerId) (p : Peer) : Device :=
  { d with
    sendWorkQueue := d.sendWorkQueue.erase pid
    peers := d.peers.insert pid
      {p with handshakePending := (d.sendWorkQueue.erase pid).contains pid} }

end Leanux.Proofs.WG.Index
