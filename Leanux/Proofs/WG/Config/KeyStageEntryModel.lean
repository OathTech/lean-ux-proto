import Leanux.Proofs.WG.Config.KeyStageModel
import Leanux.Proofs.WG.Config.ConfiguredBoundaryModel
import Leanux.Proofs.WG.Config.RequestOrderModel

/-! Historical account and exact device effects at completed private-key stages. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.KeyStage

open Leanux Leanux.WG Queues Queues.RxCredits
open Leanux.Proofs.WG.Config.OwnerConfiguration RequestOrder

def FundedEntries (cs : Ledger) (loans : Reservations) (h : List Receipt) : Prop :=
  ∀ r∈h, r.kind=.keyStage → ProjectedEntry cs loans r.before

def ReceiptEffects (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (r : Receipt) : Prop :=
  ProjectedEntry cs loans r.before ∧ r.result=0 ∧ ProjectedEntry cs loans r.after ∧
    ∃ before after, r.before.wg.device=some before ∧ r.after.wg.device=some after ∧
      Effect attrs before after

def RequestEffects (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (result : Inspection) : Prop :=
  ∀ r∈result.receipts, r.kind=.keyStage → ReceiptEffects cs loans attrs r


end Leanux.Proofs.WG.Config.KeyStage
