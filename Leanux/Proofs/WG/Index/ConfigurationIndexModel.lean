import Leanux.Proofs.WG.Index.ReachedIndexBridge
import Leanux.Proofs.WG.Index.SenderIndexModel
import Leanux.Proofs.WG.Queues.DeviceBoundary

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Lifetimes Std.Do
open Leanux.Proofs.WG.Configuration

def Entry (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  DeviceBoundary.Entry cs loans w ∧ CurrentSlots.Inv w ∧ Reached.Core w

def Acquired (cs : Ledger) (loans : Reservations) (peer : Option PeerId) (w : WGWorld) : Prop :=
  match peer with
  | none => Entry cs loans w
  | some pid => ∃ paid : Owner, paid.slot=pid ∧ Entry cs (paid::loans) w ∧
      pid ∈ BaseCoherence.slots w

def deviceFields (d : Device) := (d.nextKeypairId,senderDeviceCell d)

def fields (w : WGWorld) := w.dev.map deviceFields

end Leanux.Proofs.WG.Index.ConfigurationIndex
