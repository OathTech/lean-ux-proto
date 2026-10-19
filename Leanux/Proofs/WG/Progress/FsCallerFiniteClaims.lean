import Leanux.Proofs.WG.Progress.FsReleaseFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.FsFinite
open Leanux

/-! These projected product outcomes follow from the stronger native FS.M
source equalities. Those equalities retain all FS, task and Ambient effects,
including Stops; the campaign view itself does not expose every FS field. -/

theorem original_fopReadIter_finite (iocb : Kiocb) (count : Nat) (ops : Option FopsId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.fopReadIter iocb count ops)) (liftFS (fopReadIter iocb count ops)) := by
  rw [fopReadIter_source]
  intro w pre
  rfl

theorem original_fopWriteIter_finite (iocb : Kiocb) (src : IovIter) (ops : Option FopsId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.fopWriteIter iocb src ops)) (liftFS (fopWriteIter iocb src ops)) := by
  rw [fopWriteIter_source]
  intro w pre
  rfl

theorem original_putPipeInfo_finite (ino : PipefsInodeId) (pid : PipeId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.putPipeInfo ino pid)) (liftFS (putPipeInfo ino pid)) := by
  rw [putPipeInfo_source]
  intro w pre
  rfl

theorem original_pipeRelease_finite (ino : PipefsInodeId) (fid : FileId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.pipeRelease ino fid)) (liftFS (pipeRelease ino fid)) := by
  rw [pipeRelease_source]
  intro w pre
  rfl

theorem original_fopRelease_finite (fid : FileId) (ops : Option FopsId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.fopRelease fid ops)) (liftFS (fopRelease fid ops)) := by
  rw [fopRelease_source]
  intro w pre
  rfl

theorem original_fputFinal_finite (fid : FileId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.fputFinal fid)) (liftFS (fputFinal fid)) := by
  rw [fputFinal_source]
  intro w pre
  rfl

theorem original_fputSync_finite (fid : FileId) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.fputSync fid)) (liftFS (fputSync fid)) := by
  rw [fputSync_source]
  intro w pre
  rfl

theorem original_taskWorkRun_finite  :
    Campaign2.Product.AgreesOn (fun _ => True)
      (liftFS (Leanux.taskWorkRun )) (liftFS (taskWorkRun )) := by
  rw [taskWorkRun_source]
  intro w pre
  rfl

end Leanux.Proofs.WG.Progress.FsFinite
