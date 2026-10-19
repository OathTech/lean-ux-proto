import Leanux.Proofs.WG.Progress.PipeRoundupSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress
open Leanux

/-- Unconditional completed finite evaluation of the original pipe-size
rounding helper. Inputs and doubling retain its exact Nat semantics. The
fcntl conversion to UInt32 and roundPipeSize's overflow guard are unchanged;
this is not a whole pipe operation or whole-run termination claim. -/
theorem original_pipe_roundup_finite (target : Nat) :
    PipeRoundup.finite target = some (roundupPowOfTwoUL target) ∧
      target ≤ roundupPowOfTwoUL target :=
  PipeRoundup.finite_source target

end Leanux.Proofs.WG.Progress
