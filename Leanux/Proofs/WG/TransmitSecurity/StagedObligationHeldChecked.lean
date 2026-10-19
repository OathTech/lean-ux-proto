import Leanux.Proofs.WG.TransmitSecurity.StagedObligationCheckedCarrier
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationHeldFrontierFrames

namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.HeldChecked
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Staged.Origins AuthenticatedEffects CausalJournal HeldFrontier

/-- The actual checked send retains the same selected-ticket frontier on
every key check and reservation Stop. Only the original no-key or submission
callback may transfer ownership. Submission receives the exact ordered native
plaintext batch, including repeated payloads; its callback contract remains
explicit until the allocation/source join is discharged. -/
theorem checked (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (keypair : Option KeypairId) (Safe : List Event → Prop)
    (frontier : ∀ h, Anchor ledger debts generation pid peer position h → Safe h)
    (Post : List Event → WGWorld → Ambient → Prop)
    (postSafe : ∀ h w a, Post h w a → Safe h)
    (noKey : Option KeypairId → Bool → WGPrefix Event Unit)
    (submit : KeypairId → List DataPacket → WGPrefix Event Unit)
    (rejected : ∀ kp invalid, StatePrefixEnsures (Held ledger debts generation pid peer position) Safe
      (noKey kp invalid) (fun _ => Post))
    (submitted : ∀ kid packets, StatePrefixEnsures
      (fun h w a => Held ledger debts generation pid peer position h w a ∧
        BatchPayload.Shape pid kid peer.staged packets) Safe (submit kid packets) (fun _ => Post)) :
    StatePrefixEnsures (Held ledger debts generation pid peer position) Safe
      (RestoreEntry.checkedWith liftWGPrefix (fun kid => state (Journal.reserve kid)) noKey submit pid peer keypair)
      (fun _ => Post) :=
  CheckedCarrier.checked (Held ledger debts generation pid peer position) pid peer keypair Safe
    (fun _ _ _ before => frontier _ before.anchor)
    (held_ambient frontier) (held_world frontier) (held_read_key frontier) (reservation_held frontier)
    Post postSafe noKey submit rejected submitted

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.HeldChecked
