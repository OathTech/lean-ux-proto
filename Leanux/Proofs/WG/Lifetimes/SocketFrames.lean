import Leanux.Proofs.Framing.WGKernel
import Leanux.Proofs.Framing.Lift

/-! Seven-field WG-store frames for socket selection and pending NET_RX.
The original device and duplicate-raise guards remain part of the actions. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

theorem socketPort_sameStore (family : Nat) : SameWGStore (socketPort family) := by
  apply SameView.of_wp
  intro k
  mvcgen [socketPort, getDev, unsupported, invariant, AmbientM.unsupported, AmbientM.invariant]

theorem raiseLoopbackRx_sameStore : SameWGStore raiseLoopbackRx := by
  apply SameView.of_wp
  intro k
  mvcgen [raiseLoopbackRx, invariant, AmbientM.invariant]

end Leanux.Proofs.WG.Lifetimes
