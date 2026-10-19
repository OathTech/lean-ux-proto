import Leanux.Proofs.WG.Progress.FsFcntlFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

theorem original_roundPipeSize_finite (size : Nat) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.roundPipeSize size)) (liftFS (roundPipeSize size)) := by
  rw [roundPipeSize_source]
  intro w pre
  rfl

theorem original_pipeSetSize_finite (pid : PipeId) (arg : Nat) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.pipeSetSize pid arg)) (liftFS (pipeSetSize pid arg)) := by
  rw [pipeSetSize_source]
  intro w pre
  rfl

theorem original_pipeFcntl_finite (fid : FileId) (cmd : Nat) (arg : Nat) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.pipeFcntl fid cmd arg)) (liftFS (pipeFcntl fid cmd arg)) := by
  rw [pipeFcntl_source]
  intro w pre
  rfl

theorem original_doFcntl_finite (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) (fid : FileId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.doFcntl fd cmd arg fid)) (liftFS (doFcntl fd cmd arg fid)) := by
  rw [doFcntl_source]
  intro w pre
  rfl

theorem original_sysFcntl_finite (fd : Nat) (cmd : FcntlCmd) (arg : UInt64) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.sysFcntl fd cmd arg)) (liftFS (sysFcntl fd cmd arg)) := by
  rw [sysFcntl_source]
  intro w pre
  rfl

end Leanux.Proofs.WG.Progress.FsFinite
