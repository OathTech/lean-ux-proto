import Leanux.Proofs.WG.Config.KeyScalarSource

/-! Completed key-stage retention of surviving stamped getter scalars, including queued collision cleanup. Stops have no claimed final state. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.Configuration
theorem key_stage_keeps (entry : Campaign2.Snapshot) (attrs : DeviceAttrs) :
    Campaign2.Ensures (RequestOrder.keyStage attrs) (Keeps entry) (fun _=>Keeps entry) :=
  key_stage (observation entry) attrs
end Leanux.Proofs.WG.Config.GetterScalar
