import Leanux.Proofs.WG.Progress.PipeWriteOuterSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux

/-- Exact finite evaluation of the full original write_iter operation, retaining
the concrete wake and timestamp suffix and every original failure outcome. -/
theorem original_pipe_write_finite (iocb : Kiocb) (src : IovIter) :
    pipeWrite iocb src = PipeWriteOuter.finite iocb src :=
  PipeWriteOuter.finite_source iocb src

end Leanux.Proofs.WG.Progress
