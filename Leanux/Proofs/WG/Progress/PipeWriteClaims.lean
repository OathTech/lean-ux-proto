import Leanux.Proofs.WG.Progress.PipeWriteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux

/-- The original complete write-to-out helper has the exact structurally finite
 evaluator, for arbitrary inputs and states, including every original Stop. -/
theorem original_pipe_write_to_out_finite (iocb : Kiocb) (filp : File)
    (pid : PipeId) (src : IovIter) :
    pipeWriteToOut iocb filp pid src = PipeWrite.finite iocb filp pid src :=
  PipeWrite.finite_source iocb filp pid src

end Leanux.Proofs.WG.Progress
