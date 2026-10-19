import Leanux.Proofs.WG.Progress.PipeFreeFrames

/-! Execution equation for the actual environment-controlled copy decision. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.PipeWrite
open Leanux PipeFree

@[simp] theorem run_envOk (site : EnvSite) (f t a) :
    run (envOk site : FS.M Bool) f t a =
    ((AmbientM.envOk site).run a >>= fun (v,b)=>pure (((v,f),t),b)) := rfl

end Leanux.Proofs.WG.Progress.PipeWrite
