import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSelection

/-! The resident staged component of the fixed ledger. Equality is checked
at every epoch/peer allocation, so removing a resident queue cannot erase its
obligations merely by making a premise false. Held and allocated tickets have
separate locations and require their own source carriers. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins
open AuthenticatedEffects.CausalJournal

def pendingAt (location : Pending) (ledger : Ledger) : List Ticket :=
  ledger.filterMap fun entry => match entry.2 with
    | .pending actual => if actual = location then some entry.1 else none
    | .terminal _ => none

def stagedPackets (epoch : Nat) (pid : PeerId) (stamp : Nat) (w : WGWorld) : List Packet :=
  if Packets.epoch w = some epoch then
    match stagedAt w pid with
    | none => []
    | some (allocation,packets) => if allocation = stamp then packets else []
  else []

def QueueInv (history : List Event) (ledger : Ledger) (w : WGWorld) : Prop :=
  ∀ epoch pid stamp,
    Aligned (Born history epoch pid stamp)
      (pendingAt (.staged epoch pid stamp) ledger) (stagedPackets epoch pid stamp w)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
