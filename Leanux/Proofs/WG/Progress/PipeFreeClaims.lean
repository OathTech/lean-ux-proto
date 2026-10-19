import Leanux.Proofs.WG.Progress.PipeFreeSource

/-! Unconditional equality of the original operation with its finite evaluator.
This includes original Stop outcomes; it is not a claim of successful freeing
or of termination of an arbitrary surrounding syscall or runner. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
theorem original_free_pipe_info_finite (pid : Leanux.PipeId) :
    Leanux.freePipeInfo pid = PipeFree.finite pid :=
  PipeFree.finite_source pid
end Leanux.Proofs.WG.Progress
