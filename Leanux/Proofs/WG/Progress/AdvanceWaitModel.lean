import Leanux.Kernel.Defs

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux

/-- Bounds captured by the original recorded post-advance wait before its timer
pass. These are source reads, not an assertion that an earlier advance ran. -/
structure AdvanceWaitReceipt where
  j0 : UInt64
  j1 : UInt64
  jEnd : UInt64

/-- The original wrapped-time test; it is not an ordinary natural-number order. -/
def AdvanceWaitReceipt.pass (r : AdvanceWaitReceipt) : UInt64 :=
  if timeAfter r.jEnd r.j1 then r.jEnd else r.j0
end Leanux.Proofs.WG.Progress
