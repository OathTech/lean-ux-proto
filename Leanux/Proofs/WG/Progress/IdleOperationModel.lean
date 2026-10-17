import Leanux.Syscalls

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- The operations whose actual syscall tail ends immediately after an idle wait. -/
def HasFinalIdleWait : Syscall → Prop
  | .wgSet _ | .wgInject .. | .wgXmit .. | .wgBatch .. => True
  | _ => False

end Leanux.Proofs.WG.Progress
