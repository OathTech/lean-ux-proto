import Leanux.Proofs.WG.Queues.CurrentSlotCompletion
import Leanux.Proofs.WG.Noise.ConfirmationSequenceEffects
import Leanux.Proofs.WG.Noise.RotationSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ConsumeConfirmation
open Std.Do
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Queues MaterialOrigin

/-- Data-only observation of the original confirmation cut. -/
structure ConfirmationObservation where
  peer : PeerId
  packet : RxPacket
  endpoint : Endpoint
  entry : Campaign2.Snapshot
  before : Campaign2.Snapshot
  after : Campaign2.Snapshot
  finish : Campaign2.Snapshot
  confirmed : Bool
  value : Option (List UInt8)

def projectedStampAt (s : Campaign2.Snapshot) (id : KeypairId) : Option Nat :=
  (s.wg.device.bind fun d => d.keypairs[id]?).map Keypair.internalId

def ConfirmationObservation.Facts (r : ConfirmationObservation) : Prop :=
  ∃ (d : Device) (p : Peer) (before : Device) (read : Peer) (final : Device),
    r.entry.wg.device = some d ∧ d.peers[r.peer]? = some p ∧
    r.before.wg.device = some before ∧ before.peers[r.peer]? = some read ∧
    CurrentSlots.slotCell read = CurrentSlots.slotCell p ∧
    projectedStampAt r.before r.packet.keypair = projectedStampAt r.entry r.packet.keypair ∧
    r.after.wg.device = some final ∧
    ConfirmationEffect r.peer r.packet.keypair before read r.confirmed final ∧
    (r.confirmed = true ↔ p.keypairNext = some r.packet.keypair)

/-- A successful stamped occurrence refers to the actual entry allocation,
not the reusable numeric key slot. -/
def ConfirmationObservation.ConfirmedStamp (r : ConfirmationObservation) (stamp : Nat) : Prop :=
  r.confirmed = true ∧ projectedStampAt r.entry r.packet.keypair = some stamp


end Leanux.Proofs.WG.Noise.ConsumeConfirmation
