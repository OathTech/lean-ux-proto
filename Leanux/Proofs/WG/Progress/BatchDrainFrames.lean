import Leanux.Proofs.Framing.EnvLeaves
import Leanux.Env
import Leanux.Proofs.WG.Noise.Execution

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Device-only projection of landed C1 `Framing.deliverSent_sameKernel` in `Framing/EnvLeaves.lean`.
Actual deliveries may change fixture outputs and `sent`; their normal runs
preserve the full optional Device. -/
theorem deliverSent_sameKernel_device_variant (initial : Option Device) :
    Noise.Product.Ensures deliverSent (fun w => w.wg.dev = initial)
      (fun _ w => w.wg.dev = initial) := by
  refine (Noise.Product.ensures_iff deliverSent
    (fun w => w.wg.dev = initial) (fun _ w => w.wg.dev = initial)).mpr ?_
  exact Leanux.Proofs.Framing.deliverSent_sameKernel.wp
    (fun v => v.2.2.2.dev = initial)

end Leanux.Proofs.WG.Progress
