import Leanux.Proofs.WG.Lifetimes.SavedPeers

/-! Full-Kernel frames for concrete access-free socket/record helpers. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem socketPort_sameKernel (family : Nat) : SameKernel (socketPort family) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [socketPort, getDev, getK, unsupported, invariant]

theorem raiseLoopbackRx_sameKernel : SameKernel raiseLoopbackRx := by
  apply sameKernel_of_wp
  intro k
  mvcgen [raiseLoopbackRx, invariant]

end Leanux.Proofs.WG.Lifetimes
