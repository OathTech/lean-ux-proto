import Leanux.Proofs.WG.Config.RequestOrderSource

/-! Projected inspection data connected to one actual native request observation. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

def inspection (attrs : DeviceAttrs) (w : WGWorld) (ambient : Ambient) : Inspection :=
  let out := runWGPrefix (observe attrs) w ambient []
  ⟨Campaign2.observeResult out.1,out.2⟩

def inspect (attrs : DeviceAttrs) : WG.M Inspection := fun w ambient =>
  .ok ((inspection attrs w ambient,w),ambient)

def Matches (attrs : DeviceAttrs) (entry : Campaign2.Snapshot) (result : Inspection) : Prop :=
  ∃ w ambient, Campaign2.snapshot w ambient = entry ∧ inspection attrs w ambient = result

def InspectionFacts (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) : Prop :=
  Matches attrs entry result ∧ ValidHistory attrs result.receipts ∧
    (requestLanguage attrs).prefixes result.receipts ∧
    match result.outcome with
    | .error _ => True
    | .ok (ret,_) => (requestLanguage attrs).normal ret result.receipts

def Certificate (attrs : DeviceAttrs) (entry : Campaign2.Snapshot) (result : Inspection) : Prop :=
  InspectionFacts attrs entry result ∧ PreludeFacts attrs entry result

end Leanux.Proofs.WG.Config.RequestOrder
