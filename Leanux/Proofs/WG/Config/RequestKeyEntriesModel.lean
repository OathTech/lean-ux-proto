import Leanux.Proofs.WG.Config.RequestOrderModel

/-! A predicate over the projected entry of every completed private-key stage. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG

def KeyEntries (F : Campaign2.Snapshot → Prop) (h : List Receipt) : Prop :=
  ∀r∈h,r.kind=.keyStage → F r.before

end Leanux.Proofs.WG.Config.RequestOrder
