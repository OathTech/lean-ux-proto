import Leanux.Proofs.WG.Config.RequestOrderModel

/-! Projected nonzero port receipts and their normal request endpoint relation. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG

def PortRefused (r : Receipt) : Prop :=
  (∃ port, r.kind = .port port) ∧ r.result ≠ 0

def NoRefusal (h : List Receipt) : Prop := ∀ r ∈ h, ¬ PortRefused r

def RefusalFinal (ret : Int) (h : List Receipt) (final : Campaign2.State) : Prop :=
  ∀ r ∈ h, PortRefused r → r.result = ret ∧ r.after.wg = final

def RefusalSilent {α : Type} (L : Language α) : Prop :=
  ∀ h, L.prefixes h → NoRefusal h

def RefusalFacts (result : Inspection) : Prop :=
  match result.outcome with
  | .error _ => True
  | .ok (ret,final) => RefusalFinal ret result.receipts final.wg

end Leanux.Proofs.WG.Config.RequestOrder
