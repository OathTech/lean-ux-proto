import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationTerminalReceipt
import Leanux.Proofs.WG.TransmitSecurity.StagedTicketIdentity

/-! Fixed birth tickets have one logical location or one terminal result.
These relations are the ledger algebra; native source transport is a separate
obligation. Queue aliases and storage cleanup never create another ticket. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG
open Staged.Origins

inductive Pending where
  | staged (epoch : Nat) (peer : PeerId) (allocation : Nat)
  | selected (takePosition : Nat)
  | allocated (batchPosition ordinal : Nat)
  deriving DecidableEq

inductive Terminal where
  | counted (position : Nat) (arm : HandshakeSecurity.StagedDisposal.Arm)
  | socket (position : Nat) (succeeded : Bool)
  | sendRefused (position : Nat)
  | disposed (position : Nat) (reason : HandshakeSecurity.StagedConservation.Terminal.Reason)

inductive Status where
  | pending (location : Pending)
  | terminal (outcome : Terminal)

abbrev Ledger := List (Ticket × Status)

def keys (ledger : Ledger) : List Ticket := ledger.map Prod.fst

def Valid (births : List Ticket) (ledger : Ledger) : Prop :=
  keys ledger = births ∧ births.Nodup

/-- A native ownership transfer or first terminal cut changes a pending
obligation. A terminal outcome can only be retained, including during cleanup. -/
inductive Change : Status → Status → Prop where
  | retain (status : Status) : Change status status
  | transfer (before after : Pending) : Change (.pending before) (.pending after)
  | settle (before : Pending) (outcome : Terminal) : Change (.pending before) (.terminal outcome)

/-- An existing ticket is neither erased nor relabelled. Admission appends
fresh entries separately; the caller must justify each change at a native cut. -/
inductive Step : Ledger → Ledger → Prop where
  | nil : Step [] []
  | cons (ticket : Ticket) (change : Change before after) (tail : Step left right) :
      Step ((ticket,before) :: left) ((ticket,after) :: right)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
