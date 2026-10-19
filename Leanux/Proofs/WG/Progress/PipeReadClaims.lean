import Leanux.Proofs.WG.Progress.PipeReadSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux

/-- Exact finite evaluation of the complete original pipe read, for arbitrary
inputs and every state, including all original refusal and failure outcomes. -/
theorem original_pipe_read_finite (iocb : Kiocb) (count : Nat) :
    pipeRead iocb count = PipeRead.finite iocb count :=
  PipeRead.finite_source iocb count

end Leanux.Proofs.WG.Progress
