import Leanux.Proofs.WG.Config.RequestOrderModel
import Leanux.Proofs.WG.Config.ConfiguredBoundaryModel

/-! Projected entry and exit accounts for completed peer-command receipts. Key-before-peer is only a grammar property; no execution is reconstructed. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.FundedCommands
open Leanux Leanux.WG Queues Queues.RxCredits AllowedIps Configuration
open Leanux.Proofs.WG.Config.OwnerConfiguration

def KeyOrEmpty (h : List Receipt) : Prop :=
  peerReceipts h=[] ∨ ∃key∈h,key.kind=.keyStage

def Entries (cs : Ledger) (loans : Reservations) (h : List Receipt) : Prop :=
  ∀r∈peerReceipts h,ProjectedEntry cs loans r.before ∧ ProjectedEntry cs loans r.after

end Leanux.Proofs.WG.Config.RequestOrder.FundedCommands
