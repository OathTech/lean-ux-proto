import Leanux.Proofs.WG.Config.RequestReadbackModel
import Leanux.Proofs.WG.Config.RequestOrderInspectionBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

namespace RequestOrder

/-- The inspection and paired outcome share the actual original entry and
ambient input. This relation introduces no second runtime observer. -/
def ReadbackMatches (attrs : DeviceAttrs) (d : Device) (initial : Campaign2.Snapshot)
    (inspected : Inspection) (outcome : Campaign2.Outcome (Int × Except Int Json)) : Prop :=
  ∃ w ambient, Campaign2.snapshot w ambient = initial ∧
    inspection attrs w ambient = inspected ∧
    Campaign2.observeResult (((do
      let ret ← wgSetDevice attrs
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump)).run w).run ambient) = outcome

end RequestOrder

end Leanux.Proofs.WG.Config
