import Leanux.Proofs.WG.Config.RequestFundedCommandsEffects
import Leanux.Proofs.WG.Config.ConfiguredBoundaryBridge
import Leanux.Proofs.WG.Config.RequestOrderReceiptBridge

/-! The configured account depends on WG state, while actual receipt validity supplies the next native snapshot. Ambient branch logs need not agree. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.FundedCommands
open Leanux Leanux.WG Queues Queues.RxCredits AllowedIps Configuration
open Leanux.Proofs.WG.Config.OwnerConfiguration

theorem entry_at_snapshot (cs : Ledger) (loans : Reservations)
    (prior : Campaign2.Snapshot) (g : WGWorld) (a : Ambient)
    (pre : ProjectedEntry cs loans prior)
    (same : (Campaign2.snapshot g a).wg=prior.wg) :
    ProjectedEntry cs loans (Campaign2.snapshot g a) := by
  obtain ⟨⟨old,b,eq,input⟩,ready⟩:=pre
  subst prior
  have worlds:=Index.receiveInput_world same
  subst g
  exact (entry_snapshot cs loans old a).mpr ⟨input,ready⟩

theorem entry_at_receipt (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (prior : Campaign2.Snapshot) (r : Receipt)
    (valid : Valid attrs r) (pre : ProjectedEntry cs loans prior)
    (same : r.before.wg=prior.wg) : ProjectedEntry cs loans r.before := by
  obtain ⟨native,_,equal⟩:=valid
  rw [←equal] at same ⊢
  exact entry_at_snapshot cs loans prior native.before native.ambientBefore pre same


end Leanux.Proofs.WG.Config.RequestOrder.FundedCommands
